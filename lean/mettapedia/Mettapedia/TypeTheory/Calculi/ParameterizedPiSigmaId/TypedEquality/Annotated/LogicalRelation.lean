import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Validity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.HeadSteps
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.ProjectionLaws

/-!
# A logical relation for the annotated calculus, indexed by witnesses

Two annotated terms are related at a type, and two types are related, *as far as
a token of a witness observes* (`RT`). A witness is a compact element of the
domain, a finite list of tokens, and the relation at a witness is the relation at
each of its tokens. The clause of a token is read off its kind:

* **types.** At the tag of a former both types reduce, by typed weak-head
  reduction, to that former with judgmentally equal components: to universe heads
  that are the same up to head equality, to the type of proposition codes, to the
  numbers, to one ground type, to dependent function types, to dependent pair
  types, to identity types. A component token relates the components; a family
  entry `Z ↦ W` asks that arguments related as far as `Z` observes are sent to
  types related as far as `W` observes, three ways: each family at the two
  arguments, and the two families at one argument;
* **functions.** A function entry `X ↦ Y` asks the same of applications: each
  function at two related arguments, and the two functions at one argument;
* **pairs.** At a dependent pair type `Σ D E` the first projections are equal at `D`;
  a first-component token relates them as far as it observes, and a
  second-component token relates the second projections at `E` at the first
  projection of the left term, and at every term with a common reduct with it;
* **reflexivity.** Both terms reduce to reflexivity proofs whose points are
  judgmentally equal to the endpoints of the identity type and to each other; a
  point token relates the points and the endpoints as far as it observes;
* **numbers.** Both reduce to zero, or to successors of related numbers;
* **declared datatypes.** At the tag of a declared datatype both types reduce to its
  constant (`DataRed`); a parameter token relates the datatype's parameter to itself;
* **constructors.** At the tag of a constructor `c` of a declared datatype both terms
  reduce to `c` applied to as many terms as it has fields, the fields judgmentally equal
  one by one at their types (`CtorRed`); a field token relates the fields `i` at the
  field's type, the datatype itself or one of its parameters. Zero and the successor
  are the instances at the numbers (`ZeroRed.iff_ctorRed`, `SuccRed.iff_ctorRed`);
* **types and codes as terms.** At a universe the terms are related as types; at
  the type of proposition codes their decodings are.

A token entailed by the empty witness observes nothing, and relates everything.

The relation is defined by well-founded recursion on the **depth of the token**,
never on types or codes. It needs no compact type witness: the kind of the token
decides the clause, and a compact type witness enters only the presuppositions of
the laws. The universe of proposition codes is impredicative, and the clause of a
code is the relation of its decoding as a type: a quantifier's family is observed
at codes only through the smaller input of a family entry.

The relation is parameterized by a weak-head reduction with the properties the
clauses read (`HeadReduction`: β and the projections of pairs, the head position of
applications and projections, the root steps, the argument of the decoder,
determinism, and normal canonical forms, among them the constant of a declared
datatype and a constructor applied to as many terms as it has fields), and by the
syntactic rigid types (`RigidTypes`: the type of proposition codes and its decoder,
the numbers with zero and successor, the ground types, and the declared datatypes with
their parameters and constructors, the numbers among them).

Laws proved here:

* the relation is **closed under entailment** (`RT.closed`): a token entailed by
  the tokens of one kind of a witness relates what they all relate;
* **head expansion** along typed weak-head reduction, of terms (`RT.expand`) and of
  types (`RT.expand_ty`), and **head reduction** (`RT.reduce`, `RT.reduce_ty`): by
  determinism, a reduct of a term reducing to a canonical form reduces to it too;
* the **reflexive instance** of either side (`RT.left`), the passage between terms
  of a universe and types (`RT.toType`, `RT.ofType`), and between codes and their
  decodings (`RT.toCodes`, `RT.ofCodes`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Impredicative.Domain
open Normalization (LevelModel HeadSame)
open UniverseLevel (LevelOrder)

variable {Head : Type} {R : Rules Head}

/-! ## The rigid types and the reduction -/

/-- The syntactic types the relation reads canonical forms off, besides the type
formers: the type of proposition codes and its decoder, the numbers with zero and
successor, and the ground types. -/
structure RigidTypes (P : ChurchRules R) where
  prop : DeclName
  holds : DeclName
  num : DeclName
  zero : DeclName
  suc : DeclName
  /-- The decoder sends codes to types of a universe. -/
  holds_typed : ∀ {n : Nat} (Γ : CCtx Head n), ∃ u, R.isUniverse u ∧
    CTyped P Γ (.const holds) (.pi (.const prop) (.head u))
  /-- The ground types: the syntactic types whose only element is the least one. -/
  ground : {n : Nat} → CTm Head n → Prop
  /-- The declared datatypes, each the constant of its type. -/
  data : DeclName → Prop
  /-- The parameters of a declared datatype: the closed types of the fields that are not the
  datatype itself, numbered as the domain numbers the components of a datatype. -/
  params : DeclName → List (CTm Head 0)
  /-- The constructors of the declared datatypes: `c` builds `d` from fields of the shapes
  `fs`. -/
  ctor : DeclName → DeclName → List FieldShape → Prop
  /-- A constructor builds a declared datatype. -/
  ctor_data : ∀ {d c : DeclName} {fs : List FieldShape}, ctor d c fs → data d
  /-- Zero is a constructor of the numbers with no field. -/
  zero_ctor : ctor num zero []
  /-- The successor is a constructor of the numbers with one recursive field. -/
  suc_ctor : ctor num suc [.self]

/-- The numbers are a declared datatype. -/
theorem RigidTypes.num_data {P : ChurchRules R} (K : RigidTypes P) : K.data K.num :=
  K.ctor_data K.zero_ctor

/-- A weak-head reduction of annotated terms, with what the relation needs of it:
β, the projections of pairs, the head position of applications and projections,
the root steps of the rule package and the argument of the decoder; determinism;
and the canonical forms the relation reduces to take no step. -/
structure HeadReduction (P : ChurchRules R) (K : RigidTypes P) where
  step : {n : Nat} → CTm Head n → CTm Head n → Prop
  beta : ∀ {n : Nat} (A : CTm Head n) (b : CTm Head (n + 1)) (a : CTm Head n),
    step (.app (.lam A b) a) (CTm.inst0 a b)
  appFun : ∀ {n : Nat} {f f' : CTm Head n} (a : CTm Head n), step f f' →
    step (.app f a) (.app f' a)
  root : ∀ {n : Nat} {l r : CTm Head n}, P.computation.step l r → step l r
  holdsArg : ∀ {n : Nat} {c c' : CTm Head n}, step c c' →
    step (.app (.const K.holds) c) (.app (.const K.holds) c')
  deterministic : ∀ {n : Nat} {t u u' : CTm Head n}, step t u → step t u' → u = u'
  head_normal : ∀ {n : Nat} (h : Head) (u : CTm Head n), ¬ step (.head h) u
  pi_normal : ∀ {n : Nat} (A : CTm Head n) (B : CTm Head (n + 1)) (u : CTm Head n),
    ¬ step (.pi A B) u
  id_normal : ∀ {n : Nat} (A a b u : CTm Head n), ¬ step (.id A a b) u
  refl_normal : ∀ {n : Nat} (a u : CTm Head n), ¬ step (.refl a) u
  prop_normal : ∀ {n : Nat} (u : CTm Head n), ¬ step (.const K.prop) u
  /-- The constant of a declared datatype takes no step. -/
  data_normal : ∀ {n : Nat} {d : DeclName} (u : CTm Head n), K.data d → ¬ step (.const d) u
  /-- A constructor applied to as many terms as it has fields takes no step. -/
  ctor_normal : ∀ {n : Nat} {d c : DeclName} {fs : List FieldShape} {ms : List (CTm Head n)}
    (u : CTm Head n), K.ctor d c fs → ms.length = fs.length →
      ¬ step (CTm.appSpine (.const c) ms) u
  fstPair : ∀ {n : Nat} (a b : CTm Head n), step (.fst (.pair a b)) a
  sndPair : ∀ {n : Nat} (a b : CTm Head n), step (.snd (.pair a b)) b
  fst : ∀ {n : Nat} {p p' : CTm Head n}, step p p' → step (.fst p) (.fst p')
  snd : ∀ {n : Nat} {p p' : CTm Head n}, step p p' → step (.snd p) (.snd p')
  sigma_normal : ∀ {n : Nat} (A : CTm Head n) (B : CTm Head (n + 1)) (u : CTm Head n),
    ¬ step (.sigma A B) u
  ground_normal : ∀ {n : Nat} {g : CTm Head n} (u : CTm Head n), K.ground g → ¬ step g u

variable {P : ChurchRules R} {K : RigidTypes P} (H : HeadReduction P K)

/-- Typed weak-head reduction of types: finitely many head steps, and an equality
of types. -/
def CRedTy {n : Nat} (Γ : CCtx Head n) (A B : CTm Head n) : Prop :=
  Relation.ReflTransGen H.step A B ∧ CTypeEq P Γ A B

/-- Typed weak-head reduction of terms at a type. -/
def CRedTm {n : Nat} (Γ : CCtx Head n) (t u T : CTm Head n) : Prop :=
  Relation.ReflTransGen H.step t u ∧ CEqual P Γ t u T

/-! ## The canonical forms of the clauses -/

section Shapes

variable {n : Nat} (Γ : CCtx Head n)

/-- Both types reduce to universe heads, the same up to head equality. -/
def UnivRed (A A' : CTm Head n) : Prop :=
  ∃ h h', CRedTy H Γ A (.head h) ∧ CRedTy H Γ A' (.head h') ∧ R.isUniverse h ∧
    R.isUniverse h' ∧ HeadSame R h h'

/-- Both types reduce to dependent function types with equal components. -/
def PiRed (A A' D : CTm Head n) (E : CTm Head (n + 1)) (D' : CTm Head n)
    (E' : CTm Head (n + 1)) : Prop :=
  CRedTy H Γ A (.pi D E) ∧ CRedTy H Γ A' (.pi D' E') ∧ CTypeEq P Γ D D' ∧
    CTypeEq P (.snoc Γ D) E E'

/-- Both types reduce to dependent pair types with equal components. -/
def SigmaRed (A A' D : CTm Head n) (E : CTm Head (n + 1)) (D' : CTm Head n)
    (E' : CTm Head (n + 1)) : Prop :=
  CRedTy H Γ A (.sigma D E) ∧ CRedTy H Γ A' (.sigma D' E') ∧ CTypeEq P Γ D D' ∧
    CTypeEq P (.snoc Γ D) E E'

/-- Both types reduce to one ground type. -/
def GroundRed (A A' : CTm Head n) : Prop :=
  ∃ g, K.ground g ∧ CRedTy H Γ A g ∧ CRedTy H Γ A' g

/-- Both types reduce to identity types with equal carriers and endpoints. -/
def IdRed (A A' B x y B' x' y' : CTm Head n) : Prop :=
  CRedTy H Γ A (.id B x y) ∧ CRedTy H Γ A' (.id B' x' y') ∧ CTypeEq P Γ B B' ∧
    CEqual P Γ x x' B ∧ CEqual P Γ y y' B

/-- The type reduces to an identity type, both terms to reflexivity proofs, and
the point of the left one is equal to both endpoints and to the right point. -/
def ReflRed (T M M' B x y r r' : CTm Head n) : Prop :=
  CRedTy H Γ T (.id B x y) ∧ CRedTm H Γ M (.refl r) T ∧ CRedTm H Γ M' (.refl r') T ∧
    CEqual P Γ r x B ∧ CEqual P Γ r y B ∧ CEqual P Γ r r' B

/-- The type reduces to the numbers and both terms to zero. -/
def ZeroRed (T M M' : CTm Head n) : Prop :=
  CRedTy H Γ T (.const K.num) ∧ CRedTm H Γ M (.const K.zero) T ∧
    CRedTm H Γ M' (.const K.zero) T

/-- The type reduces to the numbers and both terms to successors of equal
numbers. -/
def SuccRed (T M M' m m' : CTm Head n) : Prop :=
  CRedTy H Γ T (.const K.num) ∧ CRedTm H Γ M (.app (.const K.suc) m) T ∧
    CRedTm H Γ M' (.app (.const K.suc) m') T ∧ CEqual P Γ m m' (.const K.num)

/-- Both types reduce to the constant of the declared datatype `d`. -/
def DataRed (d : DeclName) (A A' : CTm Head n) : Prop :=
  K.data d ∧ CRedTy H Γ A (.const d) ∧ CRedTy H Γ A' (.const d)

end Shapes

/-- The parameter `j` of the declared datatype `d`, when it has one. -/
def RigidTypes.param (K : RigidTypes P) (d : DeclName) (j : Nat) {n : Nat} :
    Option (CTm Head n) :=
  ((K.params d)[j]?).map CTm.liftClosed

/-- The type of a field of the shape `f` of a constructor of the declared datatype `d`: the
datatype itself for a recursive field, and the parameter `j` of the datatype, when it has one,
for the shape `param j`. -/
def RigidTypes.fieldType (K : RigidTypes P) (d : DeclName) {n : Nat} :
    FieldShape → Option (CTm Head n)
  | .self => some (.const d)
  | .param j => K.param d j

/-- Two lists of fields of a constructor of the declared datatype `d`, of the shapes `fs`, are
equal one by one, each at the type of its field. -/
inductive FieldsEqual (K : RigidTypes P) {n : Nat} (Γ : CCtx Head n) (d : DeclName) :
    List FieldShape → List (CTm Head n) → List (CTm Head n) → Prop
  | nil : FieldsEqual K Γ d [] [] []
  | cons {f : FieldShape} {fs : List FieldShape} {A m m' : CTm Head n}
      {ms ms' : List (CTm Head n)} :
      K.fieldType d f = some A → CEqual P Γ m m' A → FieldsEqual K Γ d fs ms ms' →
        FieldsEqual K Γ d (f :: fs) (m :: ms) (m' :: ms')

/-- The field `i` of two lists of fields of a constructor of the declared datatype `d`, of the
shapes `fs`: it has the type `A`, and it is `m` in the first list and `m'` in the second. -/
def FieldAt (K : RigidTypes P) (d : DeclName) (fs : List FieldShape) {n : Nat}
    (ms ms' : List (CTm Head n)) (i : Nat) (A m m' : CTm Head n) : Prop :=
  (∃ f, fs[i]? = some f ∧ K.fieldType d f = some A) ∧ ms[i]? = some m ∧ ms'[i]? = some m'

section Shapes

variable {n : Nat} (Γ : CCtx Head n)

/-- The type reduces to the declared datatype `d`, and both terms to its constructor `c`, with
fields of the shapes `fs`, applied to fields equal one by one. -/
def CtorRed (d c : DeclName) (fs : List FieldShape) (T M M' : CTm Head n)
    (ms ms' : List (CTm Head n)) : Prop :=
  K.ctor d c fs ∧ CRedTy H Γ T (.const d) ∧ CRedTm H Γ M (CTm.appSpine (.const c) ms) T ∧
    CRedTm H Γ M' (CTm.appSpine (.const c) ms') T ∧ FieldsEqual K Γ d fs ms ms'

end Shapes

section Instances

variable {H} {n : Nat} {Γ : CCtx Head n}

/-- **The numbers as a declared datatype**: their type clause is the datatype's. -/
theorem DataRed.num_iff {A A' : CTm Head n} :
    DataRed H Γ K.num A A' ↔ CRedTy H Γ A (.const K.num) ∧ CRedTy H Γ A' (.const K.num) :=
  ⟨fun h => h.2, fun h => ⟨K.num_data, h⟩⟩

/-- **Zero is the instance of a constructor** with no field. -/
theorem ZeroRed.iff_ctorRed {T M M' : CTm Head n} :
    ZeroRed H Γ T M M' ↔ CtorRed H Γ K.num K.zero [] T M M' [] [] :=
  ⟨fun ⟨hT, r₁, r₂⟩ => ⟨K.zero_ctor, hT, r₁, r₂, .nil⟩, fun ⟨_, hT, r₁, r₂, _⟩ => ⟨hT, r₁, r₂⟩⟩

/-- **A successor is the instance of a constructor** with one recursive field, its
predecessor. -/
theorem SuccRed.iff_ctorRed {T M M' m m' : CTm Head n} :
    SuccRed H Γ T M M' m m' ↔ CtorRed H Γ K.num K.suc [.self] T M M' [m] [m'] := by
  constructor
  · rintro ⟨hT, r₁, r₂, e⟩
    exact ⟨K.suc_ctor, hT, r₁, r₂, .cons rfl e .nil⟩
  · rintro ⟨-, hT, r₁, r₂, fe⟩
    cases fe with
    | cons hf e _ =>
        cases hf
        exact ⟨hT, r₁, r₂, e⟩

end Instances

/-- The kinds whose elements are types. -/
def typeKind : Kind → Bool
  | .univ | .ground | .codes | .nat | .pi | .sigma | .ident | .data _ => true
  | _ => false

/-! ## The relation -/

/-- **The relation at one token.** `RT Γ false t A A A'`: the types `A` and `A'`
are related as far as the type token `t` observes (the third argument is not
used). `RT Γ true t T M M'`: the terms `M` and `M'` are related at the type `T` as
far as the token `t` observes. -/
def RT {n : Nat} (Γ : CCtx Head n) : Bool → Tok → CTm Head n → CTm Head n → CTm Head n → Prop
  | false, t, _, A, A' => ent [] t = true ∨
      match t with
      | .tag .univ => UnivRed H Γ A A'
      | .tag .codes => CRedTy H Γ A (.const K.prop) ∧ CRedTy H Γ A' (.const K.prop)
      | .tag .nat => CRedTy H Γ A (.const K.num) ∧ CRedTy H Γ A' (.const K.num)
      | .tag .pi => ∃ D E D' E', PiRed H Γ A A' D E D' E'
      | .tag .ident => ∃ B x y B' x' y', IdRed H Γ A A' B x y B' x' y'
      | .arg .pi i C d => ∃ D E D' E', PiRed H Γ A A' D E D' E' ∧
          (∀ c ∈ C.attach, RT Γ false c.1 D D D') ∧ (i = 0 → RT Γ false d D D D')
      | .fn .pi C Z W => ∃ D E D' E', PiRed H Γ A A' D E D' E' ∧
          (∀ c ∈ C.attach, RT Γ false c.1 D D D') ∧
          (∀ N N', CEqual P Γ N N' D → (∀ z ∈ Z.attach, RT Γ true z.1 D N N') →
            ∀ w ∈ W.attach, RT Γ false w.1 (CTm.inst0 N E) (CTm.inst0 N E) (CTm.inst0 N' E) ∧
              RT Γ false w.1 (CTm.inst0 N E') (CTm.inst0 N E') (CTm.inst0 N' E')) ∧
          (∀ N, CTyped P Γ N D → (∀ z ∈ Z.attach, RT Γ true z.1 D N N) →
            ∀ w ∈ W.attach, RT Γ false w.1 (CTm.inst0 N E) (CTm.inst0 N E) (CTm.inst0 N E'))
      | .arg .ident i C s => ∃ B x y B' x' y', IdRed H Γ A A' B x y B' x' y' ∧
          (∀ c ∈ C.attach, RT Γ false c.1 B B B') ∧ (i = 0 → RT Γ false s B B B') ∧
          (i = 1 → RT Γ true s B x x') ∧ (i = 2 → RT Γ true s B y y')
      | .fn .ident C _ _ => ∃ B x y B' x' y', IdRed H Γ A A' B x y B' x' y' ∧
          ∀ c ∈ C.attach, RT Γ false c.1 B B B'
      | .tag .ground => GroundRed H Γ A A'
      | .tag .sigma => ∃ D E D' E', SigmaRed H Γ A A' D E D' E'
      | .arg .sigma i C d => ∃ D E D' E', SigmaRed H Γ A A' D E D' E' ∧
          (∀ c ∈ C.attach, RT Γ false c.1 D D D') ∧ (i = 0 → RT Γ false d D D D')
      | .fn .sigma C Z W => ∃ D E D' E', SigmaRed H Γ A A' D E D' E' ∧
          (∀ c ∈ C.attach, RT Γ false c.1 D D D') ∧
          (∀ N N', CEqual P Γ N N' D → (∀ z ∈ Z.attach, RT Γ true z.1 D N N') →
            ∀ w ∈ W.attach, RT Γ false w.1 (CTm.inst0 N E) (CTm.inst0 N E) (CTm.inst0 N' E) ∧
              RT Γ false w.1 (CTm.inst0 N E') (CTm.inst0 N E') (CTm.inst0 N' E')) ∧
          (∀ N, CTyped P Γ N D → (∀ z ∈ Z.attach, RT Γ true z.1 D N N) →
            ∀ w ∈ W.attach, RT Γ false w.1 (CTm.inst0 N E) (CTm.inst0 N E) (CTm.inst0 N E'))
      | .tag (.data d) => DataRed H Γ d A A'
      | .arg (.data d) i C s => DataRed H Γ d A A' ∧
          (∀ c ∈ C.attach, ∀ B : CTm Head n, K.param d 0 = some B → RT Γ false c.1 B B B) ∧
          (∀ B : CTm Head n, K.param d i = some B → RT Γ false s B B B)
      | .fn (.data d) C _ _ => DataRed H Γ d A A' ∧
          ∀ c ∈ C.attach, ∀ B : CTm Head n, K.param d 0 = some B → RT Γ false c.1 B B B
      | _ => True
  | true, t, T, M, M' => ent [] t = true ∨
      if typeKind t.kind then
        (∃ h, R.isUniverse h ∧ CRedTy H Γ T (.head h) ∧ RT Γ false t M M M') ∨
          (CRedTy H Γ T (.const K.prop) ∧
            RT Γ false t (.app (.const K.holds) M) (.app (.const K.holds) M)
              (.app (.const K.holds) M'))
      else
        match t with
        | .fn .lam _ X Y => ∀ D E, CRedTy H Γ T (.pi D E) →
            (∀ N N', CEqual P Γ N N' D → (∀ x ∈ X.attach, RT Γ true x.1 D N N') →
              ∀ y ∈ Y.attach, RT Γ true y.1 (CTm.inst0 N E) (.app M N) (.app M N') ∧
                RT Γ true y.1 (CTm.inst0 N E) (.app M' N) (.app M' N')) ∧
            (∀ N, CTyped P Γ N D → (∀ x ∈ X.attach, RT Γ true x.1 D N N) →
              ∀ y ∈ Y.attach, RT Γ true y.1 (CTm.inst0 N E) (.app M N) (.app M' N))
        | .tag .refl => ∃ B x y r r', ReflRed H Γ T M M' B x y r r'
        | .arg .refl i C s => ∃ B x y r r', ReflRed H Γ T M M' B x y r r' ∧
            (∀ c ∈ C.attach, RT Γ true c.1 B r x ∧ RT Γ true c.1 B r y ∧ RT Γ true c.1 B r r') ∧
            (i = 0 → RT Γ true s B r x ∧ RT Γ true s B r y ∧ RT Γ true s B r r')
        | .fn .refl C _ _ => ∃ B x y r r', ReflRed H Γ T M M' B x y r r' ∧
            ∀ c ∈ C.attach, RT Γ true c.1 B r x ∧ RT Γ true c.1 B r y ∧ RT Γ true c.1 B r r'
        | .tag .zero => ZeroRed H Γ T M M'
        | .tag .succ => ∃ m m', SuccRed H Γ T M M' m m'
        | .arg .succ i C s => ∃ m m', SuccRed H Γ T M M' m m' ∧
            (∀ c ∈ C.attach, RT Γ true c.1 (.const K.num) m m') ∧
            (i = 0 → RT Γ true s (.const K.num) m m')
        | .fn .succ C _ _ => ∃ m m', SuccRed H Γ T M M' m m' ∧
            ∀ c ∈ C.attach, RT Γ true c.1 (.const K.num) m m'
        | .tag .pair => ∀ D E, CRedTy H Γ T (.sigma D E) → CEqual P Γ (.fst M) (.fst M') D
        | .arg .pair i C s => ∀ D E, CRedTy H Γ T (.sigma D E) →
            CEqual P Γ (.fst M) (.fst M') D ∧
            (∀ c ∈ C.attach, RT Γ true c.1 D (.fst M) (.fst M')) ∧
            (i = 0 → RT Γ true s D (.fst M) (.fst M')) ∧
            (i = 1 → ∀ N Q, CRedTm H Γ (.fst M) Q D → CRedTm H Γ N Q D →
              RT Γ true s (CTm.inst0 N E) (.snd M) (.snd M'))
        | .fn .pair C _ _ => ∀ D E, CRedTy H Γ T (.sigma D E) →
            CEqual P Γ (.fst M) (.fst M') D ∧ ∀ c ∈ C.attach, RT Γ true c.1 D (.fst M) (.fst M')
        | .tag (.ctor d c fs) => ∃ ms ms', CtorRed H Γ d c fs T M M' ms ms'
        | .arg (.ctor d c fs) i C s => ∃ ms ms', CtorRed H Γ d c fs T M M' ms ms' ∧
            (∀ r ∈ C.attach, ∀ A m m', FieldAt K d fs ms ms' 0 A m m' → RT Γ true r.1 A m m') ∧
            (∀ A m m', FieldAt K d fs ms ms' i A m m' → RT Γ true s A m m')
        | .fn (.ctor d c fs) C _ _ => ∃ ms ms', CtorRed H Γ d c fs T M M' ms ms' ∧
            ∀ r ∈ C.attach, ∀ A m m', FieldAt K d fs ms ms' 0 A m m' → RT Γ true r.1 A m m'
        | _ => True
termination_by b t => (t.depth, if b then 1 else 0)
decreasing_by
  all_goals first
    | exact Prod.Lex.right _ (by decide)
    | exact Prod.Lex.left _ _ (Tok.depth_lt_of_mem_dep (t := .arg _ _ _ _) r.2)
    | exact Prod.Lex.left _ _ (Tok.depth_lt_of_mem_dep (t := .fn _ _ _ _) r.2)
    | exact Prod.Lex.left _ _ (depth_lt_fn_left z.2)
    | exact Prod.Lex.left _ _ (depth_lt_fn_right w.2)
    | exact Prod.Lex.left _ _ (depth_lt_fn_left x.2)
    | exact Prod.Lex.left _ _ (depth_lt_fn_right y.2)
    | exact Prod.Lex.left _ _ (Tok.depth_lt_of_mem_dep (t := .arg _ _ _ _) c.2)
    | exact Prod.Lex.left _ _ (Tok.depth_lt_of_mem_dep (t := .fn _ _ _ _) c.2)
    | exact Prod.Lex.left _ _ (depth_lt_arg _ _ _ _)

/-! ## The clauses -/

section Clauses

variable {H} {n : Nat} {Γ : CCtx Head n}

/-- A token entailed by the empty witness relates everything. -/
theorem RT.of_vacuous {b : Bool} {t : Tok} {T x x' : CTm Head n} (h : ent [] t = true) :
    RT H Γ b t T x x' := by
  cases b <;> (rw [RT.eq_def]; exact Or.inl h)

/-- The type relation does not use its third argument. -/
theorem RT.ty_irrel {t : Tok} {T T' A A' : CTm Head n} :
    RT H Γ false t T A A' ↔ RT H Γ false t T' A A' := by
  rw [RT.eq_def, RT.eq_def]

theorem ent_nil_tag (k : Kind) : ent [] (.tag k) = false := by
  rw [ent_tag]; rfl

theorem RT.ty_univ_iff {T A A' : CTm Head n} :
    RT H Γ false (.tag .univ) T A A' ↔ UnivRed H Γ A A' := by
  rw [RT.eq_def]
  simp only [ent_nil_tag, Bool.false_eq_true, false_or]

theorem RT.ty_codes_iff {T A A' : CTm Head n} :
    RT H Γ false (.tag .codes) T A A' ↔
      CRedTy H Γ A (.const K.prop) ∧ CRedTy H Γ A' (.const K.prop) := by
  rw [RT.eq_def]
  simp only [ent_nil_tag, Bool.false_eq_true, false_or]

theorem RT.ty_nat_iff {T A A' : CTm Head n} :
    RT H Γ false (.tag .nat) T A A' ↔
      CRedTy H Γ A (.const K.num) ∧ CRedTy H Γ A' (.const K.num) := by
  rw [RT.eq_def]
  simp only [ent_nil_tag, Bool.false_eq_true, false_or]

theorem RT.ty_pi_iff {T A A' : CTm Head n} :
    RT H Γ false (.tag .pi) T A A' ↔ ∃ D E D' E', PiRed H Γ A A' D E D' E' := by
  rw [RT.eq_def]
  simp only [ent_nil_tag, Bool.false_eq_true, false_or]

theorem RT.ty_ident_iff {T A A' : CTm Head n} :
    RT H Γ false (.tag .ident) T A A' ↔ ∃ B x y B' x' y', IdRed H Γ A A' B x y B' x' y' := by
  rw [RT.eq_def]
  simp only [ent_nil_tag, Bool.false_eq_true, false_or]

theorem RT.ty_argPi_iff {i : Nat} {C : List Tok} {d : Tok} {T A A' : CTm Head n} :
    RT H Γ false (.arg .pi i C d) T A A' ↔ ent [] (.arg .pi i C d) = true ∨
      ∃ D E D' E', PiRed H Γ A A' D E D' E' ∧ (∀ c ∈ C, RT H Γ false c D D D') ∧
        (i = 0 → RT H Γ false d D D D') := by
  rw [RT.eq_def]
  simp only [List.mem_attach, forall_const, Subtype.forall]

theorem RT.ty_fnPi_iff {C Z W : List Tok} {T A A' : CTm Head n} :
    RT H Γ false (.fn .pi C Z W) T A A' ↔ ent [] (.fn .pi C Z W) = true ∨
      ∃ D E D' E', PiRed H Γ A A' D E D' E' ∧ (∀ c ∈ C, RT H Γ false c D D D') ∧
        (∀ N N', CEqual P Γ N N' D → (∀ z ∈ Z, RT H Γ true z D N N') →
          ∀ w ∈ W, RT H Γ false w (CTm.inst0 N E) (CTm.inst0 N E) (CTm.inst0 N' E) ∧
            RT H Γ false w (CTm.inst0 N E') (CTm.inst0 N E') (CTm.inst0 N' E')) ∧
        (∀ N, CTyped P Γ N D → (∀ z ∈ Z, RT H Γ true z D N N) →
          ∀ w ∈ W, RT H Γ false w (CTm.inst0 N E) (CTm.inst0 N E) (CTm.inst0 N E')) := by
  rw [RT.eq_def]
  simp only [List.mem_attach, forall_const, Subtype.forall]

theorem RT.ty_argIdent_iff {i : Nat} {C : List Tok} {s : Tok} {T A A' : CTm Head n} :
    RT H Γ false (.arg .ident i C s) T A A' ↔ ent [] (.arg .ident i C s) = true ∨
      ∃ B x y B' x' y', IdRed H Γ A A' B x y B' x' y' ∧ (∀ c ∈ C, RT H Γ false c B B B') ∧
        (i = 0 → RT H Γ false s B B B') ∧ (i = 1 → RT H Γ true s B x x') ∧
        (i = 2 → RT H Γ true s B y y') := by
  rw [RT.eq_def]
  simp only [List.mem_attach, forall_const, Subtype.forall]

theorem RT.ty_fnIdent_iff {C X Y : List Tok} {T A A' : CTm Head n} :
    RT H Γ false (.fn .ident C X Y) T A A' ↔ ent [] (.fn .ident C X Y) = true ∨
      ∃ B x y B' x' y', IdRed H Γ A A' B x y B' x' y' ∧ ∀ c ∈ C, RT H Γ false c B B B' := by
  rw [RT.eq_def]
  simp only [List.mem_attach, forall_const, Subtype.forall]

theorem RT.ty_ground_iff {T A A' : CTm Head n} :
    RT H Γ false (.tag .ground) T A A' ↔ GroundRed H Γ A A' := by
  rw [RT.eq_def]
  simp only [ent_nil_tag, Bool.false_eq_true, false_or]

theorem RT.ty_sigma_iff {T A A' : CTm Head n} :
    RT H Γ false (.tag .sigma) T A A' ↔ ∃ D E D' E', SigmaRed H Γ A A' D E D' E' := by
  rw [RT.eq_def]
  simp only [ent_nil_tag, Bool.false_eq_true, false_or]

theorem RT.ty_argSigma_iff {i : Nat} {C : List Tok} {d : Tok} {T A A' : CTm Head n} :
    RT H Γ false (.arg .sigma i C d) T A A' ↔ ent [] (.arg .sigma i C d) = true ∨
      ∃ D E D' E', SigmaRed H Γ A A' D E D' E' ∧ (∀ c ∈ C, RT H Γ false c D D D') ∧
        (i = 0 → RT H Γ false d D D D') := by
  rw [RT.eq_def]
  simp only [List.mem_attach, forall_const, Subtype.forall]

theorem RT.ty_fnSigma_iff {C Z W : List Tok} {T A A' : CTm Head n} :
    RT H Γ false (.fn .sigma C Z W) T A A' ↔ ent [] (.fn .sigma C Z W) = true ∨
      ∃ D E D' E', SigmaRed H Γ A A' D E D' E' ∧ (∀ c ∈ C, RT H Γ false c D D D') ∧
        (∀ N N', CEqual P Γ N N' D → (∀ z ∈ Z, RT H Γ true z D N N') →
          ∀ w ∈ W, RT H Γ false w (CTm.inst0 N E) (CTm.inst0 N E) (CTm.inst0 N' E) ∧
            RT H Γ false w (CTm.inst0 N E') (CTm.inst0 N E') (CTm.inst0 N' E')) ∧
        (∀ N, CTyped P Γ N D → (∀ z ∈ Z, RT H Γ true z D N N) →
          ∀ w ∈ W, RT H Γ false w (CTm.inst0 N E) (CTm.inst0 N E) (CTm.inst0 N E')) := by
  rw [RT.eq_def]
  simp only [List.mem_attach, forall_const, Subtype.forall]

theorem RT.ty_data_iff {d : DeclName} {T A A' : CTm Head n} :
    RT H Γ false (.tag (.data d)) T A A' ↔ DataRed H Γ d A A' := by
  rw [RT.eq_def]
  simp only [ent_nil_tag, Bool.false_eq_true, false_or]

theorem RT.ty_param_iff {d : DeclName} {i : Nat} {C : List Tok} {s : Tok} {T A A' : CTm Head n} :
    RT H Γ false (.arg (.data d) i C s) T A A' ↔ ent [] (.arg (.data d) i C s) = true ∨
      DataRed H Γ d A A' ∧ (∀ c ∈ C, ∀ B, K.param d 0 = some B → RT H Γ false c B B B) ∧
        (∀ B, K.param d i = some B → RT H Γ false s B B B) := by
  rw [RT.eq_def]
  simp only [List.mem_attach, forall_const, Subtype.forall]

theorem RT.ty_fnData_iff {d : DeclName} {C X Y : List Tok} {T A A' : CTm Head n} :
    RT H Γ false (.fn (.data d) C X Y) T A A' ↔ ent [] (.fn (.data d) C X Y) = true ∨
      DataRed H Γ d A A' ∧ ∀ c ∈ C, ∀ B, K.param d 0 = some B → RT H Γ false c B B B := by
  rw [RT.eq_def]
  simp only [List.mem_attach, forall_const, Subtype.forall]

/-- The type relation carries no clause at the tags of the kinds of terms: no type is built
by them. -/
theorem RT.ty_tag_other {k : Kind} {T A A' : CTm Head n}
    (hk : k ≠ .univ ∧ k ≠ .codes ∧ k ≠ .nat ∧ k ≠ .pi ∧ k ≠ .ident ∧ k ≠ .ground ∧
      k ≠ .sigma ∧ ∀ d, k ≠ .data d) :
    RT H Γ false (.tag k) T A A' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hk
  rw [RT.eq_def]
  refine .inr ?_
  cases k <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 |
    exact absurd rfl h4 | exact absurd rfl h5 | exact absurd rfl h6 | exact absurd rfl h7 |
    exact absurd rfl (h8 _) | trivial

/-- The type relation carries no clause at the components of the kinds whose types have no
components: the universes, the codes, the numbers, the ground types, and the kinds of
terms. -/
theorem RT.ty_arg_other {k : Kind} {i : Nat} {C : List Tok} {s : Tok} {T A A' : CTm Head n}
    (hk : k ≠ .pi ∧ k ≠ .ident ∧ k ≠ .sigma ∧ ∀ d, k ≠ .data d) :
    RT H Γ false (.arg k i C s) T A A' := by
  obtain ⟨h1, h2, h3, h4⟩ := hk
  rw [RT.eq_def]
  refine .inr ?_
  cases k <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 |
    exact absurd rfl (h4 _) | trivial

/-- The type relation carries no clause at the step functions of the kinds whose types have
no family: the universes, the codes, the numbers, the ground types, and the kinds of terms. -/
theorem RT.ty_fn_other {k : Kind} {C X Y : List Tok} {T A A' : CTm Head n}
    (hk : k ≠ .pi ∧ k ≠ .ident ∧ k ≠ .sigma ∧ ∀ d, k ≠ .data d) :
    RT H Γ false (.fn k C X Y) T A A' := by
  obtain ⟨h1, h2, h3, h4⟩ := hk
  rw [RT.eq_def]
  refine .inr ?_
  cases k <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 |
    exact absurd rfl (h4 _) | trivial

/-- At a token of a type kind, terms are related as types at a universe, and their
decodings are at the type of proposition codes. -/
theorem RT.tm_type_iff {t : Tok} (ht : typeKind t.kind = true) {T M M' : CTm Head n} :
    RT H Γ true t T M M' ↔ ent [] t = true ∨
      (∃ h, R.isUniverse h ∧ CRedTy H Γ T (.head h) ∧ RT H Γ false t M M M') ∨
        (CRedTy H Γ T (.const K.prop) ∧
          RT H Γ false t (.app (.const K.holds) M) (.app (.const K.holds) M)
            (.app (.const K.holds) M')) := by
  rw [RT.eq_def]
  simp only [ht, if_true]

theorem RT.tm_lam_iff {C X Y : List Tok} {T M M' : CTm Head n} :
    RT H Γ true (.fn .lam C X Y) T M M' ↔ ent [] (.fn .lam C X Y) = true ∨
      ∀ D E, CRedTy H Γ T (.pi D E) →
        (∀ N N', CEqual P Γ N N' D → (∀ x ∈ X, RT H Γ true x D N N') →
          ∀ y ∈ Y, RT H Γ true y (CTm.inst0 N E) (.app M N) (.app M N') ∧
            RT H Γ true y (CTm.inst0 N E) (.app M' N) (.app M' N')) ∧
        (∀ N, CTyped P Γ N D → (∀ x ∈ X, RT H Γ true x D N N) →
          ∀ y ∈ Y, RT H Γ true y (CTm.inst0 N E) (.app M N) (.app M' N)) := by
  rw [RT.eq_def]
  simp only [Tok.kind, typeKind, Bool.false_eq_true, if_false, List.mem_attach, forall_const,
    Subtype.forall]

theorem RT.tm_reflTag_iff {T M M' : CTm Head n} :
    RT H Γ true (.tag .refl) T M M' ↔ ∃ B x y r r', ReflRed H Γ T M M' B x y r r' := by
  rw [RT.eq_def]
  simp only [ent_nil_tag, Bool.false_eq_true, false_or, Tok.kind, typeKind, if_false]

theorem RT.tm_argRefl_iff {i : Nat} {C : List Tok} {s : Tok} {T M M' : CTm Head n} :
    RT H Γ true (.arg .refl i C s) T M M' ↔ ent [] (.arg .refl i C s) = true ∨
      ∃ B x y r r', ReflRed H Γ T M M' B x y r r' ∧
        (∀ c ∈ C, RT H Γ true c B r x ∧ RT H Γ true c B r y ∧ RT H Γ true c B r r') ∧
        (i = 0 → RT H Γ true s B r x ∧ RT H Γ true s B r y ∧ RT H Γ true s B r r') := by
  rw [RT.eq_def]
  simp only [Tok.kind, typeKind, Bool.false_eq_true, if_false, List.mem_attach, forall_const,
    Subtype.forall]

theorem RT.tm_fnRefl_iff {C X Y : List Tok} {T M M' : CTm Head n} :
    RT H Γ true (.fn .refl C X Y) T M M' ↔ ent [] (.fn .refl C X Y) = true ∨
      ∃ B x y r r', ReflRed H Γ T M M' B x y r r' ∧
        ∀ c ∈ C, RT H Γ true c B r x ∧ RT H Γ true c B r y ∧ RT H Γ true c B r r' := by
  rw [RT.eq_def]
  simp only [Tok.kind, typeKind, Bool.false_eq_true, if_false, List.mem_attach, forall_const,
    Subtype.forall]

theorem RT.tm_zero_iff {T M M' : CTm Head n} :
    RT H Γ true (.tag .zero) T M M' ↔ ZeroRed H Γ T M M' := by
  rw [RT.eq_def]
  simp only [ent_nil_tag, Bool.false_eq_true, false_or, Tok.kind, typeKind, if_false]

theorem RT.tm_succTag_iff {T M M' : CTm Head n} :
    RT H Γ true (.tag .succ) T M M' ↔ ∃ m m', SuccRed H Γ T M M' m m' := by
  rw [RT.eq_def]
  simp only [ent_nil_tag, Bool.false_eq_true, false_or, Tok.kind, typeKind, if_false]

theorem RT.tm_argSucc_iff {i : Nat} {C : List Tok} {s : Tok} {T M M' : CTm Head n} :
    RT H Γ true (.arg .succ i C s) T M M' ↔ ent [] (.arg .succ i C s) = true ∨
      ∃ m m', SuccRed H Γ T M M' m m' ∧ (∀ c ∈ C, RT H Γ true c (.const K.num) m m') ∧
        (i = 0 → RT H Γ true s (.const K.num) m m') := by
  rw [RT.eq_def]
  simp only [Tok.kind, typeKind, Bool.false_eq_true, if_false, List.mem_attach, forall_const,
    Subtype.forall]

theorem RT.tm_fnSucc_iff {C X Y : List Tok} {T M M' : CTm Head n} :
    RT H Γ true (.fn .succ C X Y) T M M' ↔ ent [] (.fn .succ C X Y) = true ∨
      ∃ m m', SuccRed H Γ T M M' m m' ∧ ∀ c ∈ C, RT H Γ true c (.const K.num) m m' := by
  rw [RT.eq_def]
  simp only [Tok.kind, typeKind, Bool.false_eq_true, if_false, List.mem_attach, forall_const,
    Subtype.forall]

theorem RT.tm_pairTag_iff {T M M' : CTm Head n} :
    RT H Γ true (.tag .pair) T M M' ↔
      ∀ D E, CRedTy H Γ T (.sigma D E) → CEqual P Γ (.fst M) (.fst M') D := by
  rw [RT.eq_def]
  simp only [ent_nil_tag, Bool.false_eq_true, false_or, Tok.kind, typeKind, if_false]

theorem RT.tm_argPair_iff {i : Nat} {C : List Tok} {s : Tok} {T M M' : CTm Head n} :
    RT H Γ true (.arg .pair i C s) T M M' ↔ ent [] (.arg .pair i C s) = true ∨
      ∀ D E, CRedTy H Γ T (.sigma D E) →
        CEqual P Γ (.fst M) (.fst M') D ∧ (∀ c ∈ C, RT H Γ true c D (.fst M) (.fst M')) ∧
        (i = 0 → RT H Γ true s D (.fst M) (.fst M')) ∧
        (i = 1 → ∀ N Q, CRedTm H Γ (.fst M) Q D → CRedTm H Γ N Q D →
          RT H Γ true s (CTm.inst0 N E) (.snd M) (.snd M')) := by
  rw [RT.eq_def]
  simp only [Tok.kind, typeKind, Bool.false_eq_true, if_false, List.mem_attach, forall_const,
    Subtype.forall]

theorem RT.tm_fnPair_iff {C X Y : List Tok} {T M M' : CTm Head n} :
    RT H Γ true (.fn .pair C X Y) T M M' ↔ ent [] (.fn .pair C X Y) = true ∨
      ∀ D E, CRedTy H Γ T (.sigma D E) →
        CEqual P Γ (.fst M) (.fst M') D ∧ ∀ c ∈ C, RT H Γ true c D (.fst M) (.fst M') := by
  rw [RT.eq_def]
  simp only [Tok.kind, typeKind, Bool.false_eq_true, if_false, List.mem_attach, forall_const,
    Subtype.forall]

theorem RT.tm_ctorTag_iff {d c : DeclName} {fs : List FieldShape} {T M M' : CTm Head n} :
    RT H Γ true (.tag (.ctor d c fs)) T M M' ↔ ∃ ms ms', CtorRed H Γ d c fs T M M' ms ms' := by
  rw [RT.eq_def]
  simp only [ent_nil_tag, Bool.false_eq_true, false_or, Tok.kind, typeKind, if_false]

theorem RT.tm_field_iff {d c : DeclName} {fs : List FieldShape} {i : Nat} {C : List Tok}
    {s : Tok} {T M M' : CTm Head n} :
    RT H Γ true (.arg (.ctor d c fs) i C s) T M M' ↔ ent [] (.arg (.ctor d c fs) i C s) = true ∨
      ∃ ms ms', CtorRed H Γ d c fs T M M' ms ms' ∧
        (∀ r ∈ C, ∀ A m m', FieldAt K d fs ms ms' 0 A m m' → RT H Γ true r A m m') ∧
        (∀ A m m', FieldAt K d fs ms ms' i A m m' → RT H Γ true s A m m') := by
  rw [RT.eq_def]
  simp only [Tok.kind, typeKind, Bool.false_eq_true, if_false, List.mem_attach, forall_const,
    Subtype.forall]

theorem RT.tm_fnCtor_iff {d c : DeclName} {fs : List FieldShape} {C X Y : List Tok}
    {T M M' : CTm Head n} :
    RT H Γ true (.fn (.ctor d c fs) C X Y) T M M' ↔ ent [] (.fn (.ctor d c fs) C X Y) = true ∨
      ∃ ms ms', CtorRed H Γ d c fs T M M' ms ms' ∧
        ∀ r ∈ C, ∀ A m m', FieldAt K d fs ms ms' 0 A m m' → RT H Γ true r A m m' := by
  rw [RT.eq_def]
  simp only [Tok.kind, typeKind, Bool.false_eq_true, if_false, List.mem_attach, forall_const,
    Subtype.forall]

/-- The term relation carries no clause at the tokens of the kinds of terms that no term
asserts: the tag and the components of a function, and the components and the step
functions of zero. -/
theorem RT.tm_other {t : Tok} {T M M' : CTm Head n}
    (hk : typeKind t.kind = false) (hl : ∀ C X Y, t ≠ .fn .lam C X Y) (hr : t.kind ≠ .refl)
    (hz : t ≠ .tag .zero) (hs : t.kind ≠ .succ) (hp : t.kind ≠ .pair)
    (hc : ∀ d c fs, t.kind ≠ .ctor d c fs) :
    RT H Γ true t T M M' := by
  rw [RT.eq_def]
  refine .inr ?_
  simp only [hk, Bool.false_eq_true, if_false]
  cases t with
  | tag k =>
      cases k
      case pair => exact absurd rfl hp
      case ctor d c fs => exact absurd rfl (hc d c fs)
      all_goals trivial
  | arg k i C s =>
      cases k
      case pair => exact absurd rfl hp
      case ctor d c fs => exact absurd rfl (hc d c fs)
      all_goals trivial
  | fn k C X Y =>
      cases k
      case lam => exact absurd rfl (hl C X Y)
      case pair => exact absurd rfl hp
      case ctor d c fs => exact absurd rfl (hc d c fs)
      all_goals trivial

end Clauses

/-! ## Reduction -/

section Reduction

variable {H} {n : Nat}

/-- A term that takes no head step. -/
def HeadReduction.Normal (t : CTm Head n) : Prop := ∀ u, ¬ H.step t u

/-- The first step of a reduction sequence, without choice. -/
theorem rtg_head {α : Type} {r : α → α → Prop} {a b : α} (h : Relation.ReflTransGen r a b) :
    a = b ∨ ∃ c, r a c ∧ Relation.ReflTransGen r c b := by
  induction h with
  | refl => exact .inl rfl
  | tail _ step ih =>
      rcases ih with rfl | ⟨c, h₁, h₂⟩
      · exact .inr ⟨_, step, .refl⟩
      · exact .inr ⟨c, h₁, h₂.tail step⟩

/-- A normal term reduces only to itself. -/
theorem HeadReduction.red_normal {t u : CTm Head n} (normal : H.Normal t)
    (red : Relation.ReflTransGen H.step t u) : u = t := by
  rcases rtg_head red with rfl | ⟨c, s, _⟩
  · rfl
  · exact absurd s (normal c)

/-- Every reduct of a term reduces to the normal form the term reduces to. -/
theorem HeadReduction.to_normal {t u v : CTm Head n} (r₁ : Relation.ReflTransGen H.step t u)
    (normal : H.Normal u) (r₂ : Relation.ReflTransGen H.step t v) :
    Relation.ReflTransGen H.step v u := by
  induction r₂ with
  | refl => exact r₁
  | tail _ s ih =>
      rcases rtg_head ih with rfl | ⟨c, s', rest⟩
      · exact absurd s (normal _)
      · rw [H.deterministic s s']
        exact rest

/-- **Unique normal forms.** -/
theorem HeadReduction.nf_unique {t u u' : CTm Head n} (r₁ : Relation.ReflTransGen H.step t u)
    (r₂ : Relation.ReflTransGen H.step t u') (n₁ : H.Normal u) (n₂ : H.Normal u') : u = u' :=
  H.red_normal n₂ (H.to_normal r₁ n₁ r₂)

/-- **Reductions from one term are ordered**: one continues the other. -/
theorem HeadReduction.red_linear {t u v : CTm Head n} (r₁ : Relation.ReflTransGen H.step t u)
    (r₂ : Relation.ReflTransGen H.step t v) :
    Relation.ReflTransGen H.step u v ∨ Relation.ReflTransGen H.step v u := by
  induction r₂ with
  | refl => exact .inr r₁
  | tail _ s ih =>
      rcases ih with h | h
      · exact .inl (h.tail s)
      · rcases rtg_head h with rfl | ⟨c', s', rest⟩
        · exact .inl (.single s)
        · rw [H.deterministic s s']
          exact .inr rest

theorem HeadReduction.normal_head (h : Head) : H.Normal (.head h : CTm Head n) :=
  H.head_normal h

theorem HeadReduction.normal_pi (A : CTm Head n) (B : CTm Head (n + 1)) : H.Normal (.pi A B) :=
  H.pi_normal A B

theorem HeadReduction.normal_id (A a b : CTm Head n) : H.Normal (.id A a b) :=
  H.id_normal A a b

theorem HeadReduction.normal_refl (a : CTm Head n) : H.Normal (.refl a) := H.refl_normal a

theorem HeadReduction.normal_prop : H.Normal (.const K.prop : CTm Head n) := H.prop_normal

theorem HeadReduction.normal_data {d : DeclName} (hd : K.data d) :
    H.Normal (.const d : CTm Head n) :=
  fun u => H.data_normal u hd

theorem HeadReduction.normal_ctor {d c : DeclName} {fs : List FieldShape} {ms : List (CTm Head n)}
    (hc : K.ctor d c fs) (hl : ms.length = fs.length) :
    H.Normal (CTm.appSpine (.const c) ms) :=
  fun u => H.ctor_normal u hc hl

theorem HeadReduction.normal_num : H.Normal (.const K.num : CTm Head n) :=
  H.normal_data K.num_data

theorem HeadReduction.normal_zero : H.Normal (.const K.zero : CTm Head n) :=
  H.normal_ctor (ms := []) K.zero_ctor rfl

theorem HeadReduction.normal_suc (m : CTm Head n) : H.Normal (.app (.const K.suc) m) :=
  H.normal_ctor (ms := [m]) K.suc_ctor rfl

/-- The head position of an application follows a reduction of the function. -/
theorem HeadReduction.red_app {f f' : CTm Head n} (red : Relation.ReflTransGen H.step f f')
    (a : CTm Head n) : Relation.ReflTransGen H.step (.app f a) (.app f' a) := by
  induction red with
  | refl => exact .refl
  | tail _ s ih => exact ih.tail (H.appFun a s)

/-- The argument of the decoder follows a reduction of the code. -/
theorem HeadReduction.red_holds {c c' : CTm Head n} (red : Relation.ReflTransGen H.step c c') :
    Relation.ReflTransGen H.step (.app (.const K.holds) c) (.app (.const K.holds) c') := by
  induction red with
  | refl => exact .refl
  | tail _ s ih => exact ih.tail (H.holdsArg s)

theorem HeadReduction.normal_sigma (A : CTm Head n) (B : CTm Head (n + 1)) :
    H.Normal (.sigma A B) :=
  H.sigma_normal A B

theorem HeadReduction.normal_ground {g : CTm Head n} (hg : K.ground g) : H.Normal g :=
  fun u => H.ground_normal u hg

/-- The first projection follows a reduction of the pair. -/
theorem HeadReduction.red_fst {p p' : CTm Head n} (red : Relation.ReflTransGen H.step p p') :
    Relation.ReflTransGen H.step (.fst p) (.fst p') := by
  induction red with
  | refl => exact .refl
  | tail _ s ih => exact ih.tail (H.fst s)

/-- The second projection follows a reduction of the pair. -/
theorem HeadReduction.red_snd {p p' : CTm Head n} (red : Relation.ReflTransGen H.step p p') :
    Relation.ReflTransGen H.step (.snd p) (.snd p') := by
  induction red with
  | refl => exact .refl
  | tail _ s ih => exact ih.tail (H.snd s)

end Reduction

section TypedReduction

variable {H} {L : Type} [LevelOrder L] {n : Nat} {Γ : CCtx Head n}

theorem CRedTy.trans (levels : LevelModel R L) {A B C : CTm Head n} (r₁ : CRedTy H Γ A B)
    (r₂ : CRedTy H Γ B C) : CRedTy H Γ A C :=
  ⟨r₁.1.trans r₂.1, CTypeEq.trans levels r₁.2 r₂.2⟩

theorem CRedTm.trans {a b c T : CTm Head n} (r₁ : CRedTm H Γ a b T) (r₂ : CRedTm H Γ b c T) :
    CRedTm H Γ a c T :=
  ⟨r₁.1.trans r₂.1, .trans r₁.2 r₂.2⟩

theorem CRedTy.refl {A : CTm Head n} (type : CIsType P Γ A) : CRedTy H Γ A A :=
  ⟨.refl, type.refl⟩

theorem CRedTm.refl {a T : CTm Head n} (typed : CTyped P Γ a T) : CRedTm H Γ a a T :=
  ⟨.refl, .refl typed⟩

theorem CRedTm.convType {a b T T' : CTm Head n} (r : CRedTm H Γ a b T) (e : CTypeEq P Γ T T') :
    CRedTm H Γ a b T' :=
  ⟨r.1, r.2.convType e⟩

/-- Two typed reductions of one type to normal forms reach the same one. -/
theorem CRedTy.nf_unique {A X Y : CTm Head n} (r₁ : CRedTy H Γ A X) (r₂ : CRedTy H Γ A Y)
    (n₁ : H.Normal X) (n₂ : H.Normal Y) : X = Y :=
  H.nf_unique r₁.1 r₂.1 n₁ n₂

theorem CRedTm.nf_unique {a x y T T' : CTm Head n} (r₁ : CRedTm H Γ a x T) (r₂ : CRedTm H Γ a y T')
    (n₁ : H.Normal x) (n₂ : H.Normal y) : x = y :=
  H.nf_unique r₁.1 r₂.1 n₁ n₂

/-- An equality of types, symmetric. -/
theorem CEqual.left {a b T : CTm Head n} (e : CEqual P Γ a b T) : CEqual P Γ a a T :=
  .trans e (.symm e)

theorem CTypeEq.left {A B : CTm Head n} (e : CTypeEq P Γ A B) : CTypeEq P Γ A A := by
  obtain ⟨u, hu, e⟩ := e
  exact ⟨u, hu, e.left⟩

/-- A type that reduces to a normal form, and to another type, is followed by the
other type to that normal form. -/
theorem CRedTy.reduce (levels : LevelModel R L) {A B X : CTm Head n} (rAB : CRedTy H Γ A B)
    (rAX : CRedTy H Γ A X) (normal : H.Normal X) : CRedTy H Γ B X :=
  ⟨H.to_normal rAX.1 normal rAB.1, CTypeEq.trans levels rAB.2.symm rAX.2⟩

/-- A term that reduces to a normal form at a type, and to another term, is followed
by the other term to that normal form. -/
theorem CRedTm.reduce {a b x T T' : CTm Head n} (rab : CRedTm H Γ a b T) (rax : CRedTm H Γ a x T')
    (normal : H.Normal x) (e : CTypeEq P Γ T T') : CRedTm H Γ b x T' :=
  ⟨H.to_normal rax.1 normal rab.1, .trans (.symm (rab.2.convType e)) rax.2⟩

/-- **A common reduct is kept along a reduction**: a term joining `x` at a type
joins every reduct of `x` there. -/
theorem CRedTm.join_of_red {x y N Q T : CTm Head n} (rxy : CRedTm H Γ x y T)
    (rxQ : CRedTm H Γ x Q T) (rNQ : CRedTm H Γ N Q T) :
    ∃ Q', CRedTm H Γ y Q' T ∧ CRedTm H Γ N Q' T := by
  rcases H.red_linear rxy.1 rxQ.1 with h | h
  · exact ⟨Q, ⟨h, .trans (.symm rxy.2) rxQ.2⟩, rNQ⟩
  · exact ⟨y, ⟨.refl, CEqual.left (.symm rxy.2)⟩,
      ⟨rNQ.1.trans h, .trans rNQ.2 (.trans (.symm rxQ.2) rxy.2)⟩⟩

end TypedReduction

/-! ## Entailment reads one kind of tokens -/

section Tokens

/-- The tokens of a list of kind `k`. -/
def ofKind (k : Kind) (v : List Tok) : List Tok := v.filter fun s => s.kind == k

theorem mem_ofKind {k : Kind} {v : List Tok} {s : Tok} : s ∈ ofKind k v ↔ s ∈ v ∧ s.kind = k := by
  simp [ofKind]

theorem hasTag_ofKind (k : Kind) (v : List Tok) : hasTag k (ofKind k v) = hasTag k v := by
  rw [Bool.eq_iff_iff, hasTag_iff, hasTag_iff, mem_ofKind]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

theorem args_ofKind (k : Kind) (i : Nat) (v : List Tok) : args k i (ofKind k v) = args k i v := by
  induction v with
  | nil => rfl
  | cons s v ih =>
      simp only [ofKind, List.filter_cons] at ih ⊢
      split
      · rename_i hs
        simp only [args, ih]
      · rename_i hs
        have hk : s.kind ≠ k := fun e => hs (by simp [e])
        rw [ih]
        cases s with
        | tag k' => simp [args, Tok.dep]
        | arg k' i' C t =>
            have : k' ≠ k := hk
            simp [args, Tok.kind, this]
        | fn k' C X Y =>
            have : k' ≠ k := hk
            simp [args, Tok.kind, this]

theorem fns_ofKind (k : Kind) (v : List Tok) : fns k (ofKind k v) = fns k v := by
  induction v with
  | nil => rfl
  | cons s v ih =>
      simp only [ofKind, List.filter_cons] at ih ⊢
      split
      · rename_i hs
        cases s with
        | tag k' => simpa [fns] using ih
        | arg k' i' C t => simpa [fns] using ih
        | fn k' C X Y => simp [fns, ih]
      · rename_i hs
        have hk : s.kind ≠ k := fun e => hs (by simp [e])
        rw [ih]
        cases s with
        | tag k' => rfl
        | arg k' i' C t => rfl
        | fn k' C X Y =>
            have : k' ≠ k := hk
            simp [fns, this]

theorem fnApp_ofKind (k : Kind) (v X : List Tok) : fnApp k (ofKind k v) X = fnApp k v X := by
  simp only [fnApp, fns_ofKind]

/-- **Entailment of a token reads only the tokens of its kind.** -/
theorem ent_ofKind (v : List Tok) (t : Tok) : ent (ofKind t.kind v) t = ent v t := by
  cases t with
  | tag k => rw [ent_tag, ent_tag]; exact hasTag_ofKind k v
  | arg k i C d => rw [ent_arg, ent_arg]; simp only [Tok.kind, args_ofKind]
  | fn k C X Y => rw [ent_fn, ent_fn]; simp only [Tok.kind, args_ofKind, fnApp_ofKind]

/-- A list on which a test fails somewhere has an element that fails it, without
choice. -/
theorem exists_of_all_false {α : Type} {p : α → Bool} :
    ∀ {l : List α}, l.all p = false → ∃ x ∈ l, p x = false
  | [], h => by cases h
  | a :: l, h => by
      cases ha : p a with
      | false => exact ⟨a, List.mem_cons_self, ha⟩
      | true =>
          rw [List.all_cons, ha, Bool.true_and] at h
          obtain ⟨x, hx, hpx⟩ := exists_of_all_false h
          exact ⟨x, List.mem_cons_of_mem _ hx, hpx⟩

/-- **A token entailed by a list, but not by the empty one, is entailed through a
token of its kind that is not entailed by the empty list.** -/
theorem source_of_ent {v : List Tok} {t : Tok} (e : ent v t = true) (hn : ent [] t = false) :
    ∃ s ∈ v, s.kind = t.kind ∧ ent [] s = false := by
  cases hall : (ofKind t.kind v).all (fun s => ent [] s) with
  | true =>
      have hle : ofKind t.kind v ⊑ [] := fun s hs => List.all_eq_true.1 hall s hs
      have h' := ent_cut (by rw [ent_ofKind]; exact e) hle
      rw [h'] at hn
      exact absurd hn (by decide)
  | false =>
      obtain ⟨s, hs, hsn⟩ := exists_of_all_false hall
      obtain ⟨hs, hk⟩ := mem_ofKind.1 hs
      exact ⟨s, hs, hk, hsn⟩

/-- The components of a token entailed by the empty list are. -/
theorem vacuous_dep {s : Tok} (hs : ent [] s = true) {c : Tok} (hc : c ∈ s.dep) :
    ent [] c = true := by
  cases s with
  | tag k => cases hc
  | arg k i C t =>
      rw [ent_arg, Bool.and_eq_true, List.all_eq_true] at hs
      exact hs.1 c hc
  | fn k C X Y =>
      rw [ent_fn, Bool.and_eq_true, List.all_eq_true] at hs
      exact hs.1 c hc

theorem vacuous_arg {k : Kind} {i : Nat} {C : List Tok} {t : Tok}
    (hs : ent [] (.arg k i C t) = true) : ent [] t = true := by
  rw [ent_arg, Bool.and_eq_true] at hs
  exact hs.2

theorem vacuous_out {k : Kind} {C X Y : List Tok} (hs : ent [] (.fn k C X Y) = true) {y : Tok}
    (hy : y ∈ Y) : ent [] y = true := by
  rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hs
  exact hs.2 y hy

end Tokens

/-! ## Aligning reducts -/

section Align

variable {H} {n : Nat} {Γ : CCtx Head n}

theorem CRedTy.pi_align {A D D₁ : CTm Head n} {E E₁ : CTm Head (n + 1)}
    (r : CRedTy H Γ A (.pi D E)) (r₁ : CRedTy H Γ A (.pi D₁ E₁)) : D₁ = D ∧ E₁ = E := by
  have e := CRedTy.nf_unique r₁ r (H.normal_pi _ _) (H.normal_pi _ _)
  injection e with _ h1 h2
  exact ⟨h1, h2⟩

theorem CRedTy.id_align {A B x y B₁ x₁ y₁ : CTm Head n} (r : CRedTy H Γ A (.id B x y))
    (r₁ : CRedTy H Γ A (.id B₁ x₁ y₁)) : B₁ = B ∧ x₁ = x ∧ y₁ = y := by
  have e := CRedTy.nf_unique r₁ r (H.normal_id _ _ _) (H.normal_id _ _ _)
  injection e with _ h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem CRedTm.refl_align {M r r₁ T T' : CTm Head n} (h : CRedTm H Γ M (.refl r) T)
    (h₁ : CRedTm H Γ M (.refl r₁) T') : r₁ = r := by
  have e := CRedTm.nf_unique h₁ h (H.normal_refl _) (H.normal_refl _)
  injection e

theorem CRedTm.suc_align {M m m₁ T T' : CTm Head n} (h : CRedTm H Γ M (.app (.const K.suc) m) T)
    (h₁ : CRedTm H Γ M (.app (.const K.suc) m₁) T') : m₁ = m := by
  have e := CRedTm.nf_unique h₁ h (H.normal_suc _) (H.normal_suc _)
  injection e

/-- A type does not reduce both to a universe head and to the type of codes. -/
theorem CRedTy.head_ne_prop {T : CTm Head n} {h : Head} (r : CRedTy H Γ T (.head h))
    (r' : CRedTy H Γ T (.const K.prop)) : False := by
  have e := CRedTy.nf_unique r r' (H.normal_head _) H.normal_prop
  cases e

theorem PiRed.align {A A' D D' D₁ D₁' : CTm Head n} {E E' E₁ E₁' : CTm Head (n + 1)}
    (hp : PiRed H Γ A A' D E D' E')
    (hp₁ : PiRed H Γ A A' D₁ E₁ D₁' E₁') : D₁ = D ∧ E₁ = E ∧ D₁' = D' ∧ E₁' = E' := by
  obtain ⟨h1, h2⟩ := CRedTy.pi_align hp.1 hp₁.1
  obtain ⟨h3, h4⟩ := CRedTy.pi_align hp.2.1 hp₁.2.1
  exact ⟨h1, h2, h3, h4⟩

theorem IdRed.align {A A' B x y B' x' y' B₁ x₁ y₁ B₁' x₁' y₁' : CTm Head n}
    (hi : IdRed H Γ A A' B x y B' x' y') (hi₁ : IdRed H Γ A A' B₁ x₁ y₁ B₁' x₁' y₁') :
    B₁ = B ∧ x₁ = x ∧ y₁ = y ∧ B₁' = B' ∧ x₁' = x' ∧ y₁' = y' := by
  obtain ⟨h1, h2, h3⟩ := CRedTy.id_align hi.1 hi₁.1
  obtain ⟨h4, h5, h6⟩ := CRedTy.id_align hi.2.1 hi₁.2.1
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem ReflRed.align {T M M' B x y r r' B₁ x₁ y₁ r₁ r₁' : CTm Head n}
    (h : ReflRed H Γ T M M' B x y r r') (h₁ : ReflRed H Γ T M M' B₁ x₁ y₁ r₁ r₁') :
    B₁ = B ∧ x₁ = x ∧ y₁ = y ∧ r₁ = r ∧ r₁' = r' := by
  obtain ⟨h1, h2, h3⟩ := CRedTy.id_align h.1 h₁.1
  exact ⟨h1, h2, h3, CRedTm.refl_align h.2.1 h₁.2.1, CRedTm.refl_align h.2.2.1 h₁.2.2.1⟩

theorem SuccRed.align {T M M' m m' m₁ m₁' : CTm Head n} (h : SuccRed H Γ T M M' m m')
    (h₁ : SuccRed H Γ T M M' m₁ m₁') : m₁ = m ∧ m₁' = m' :=
  ⟨CRedTm.suc_align h.2.1 h₁.2.1, CRedTm.suc_align h.2.2.1 h₁.2.2.1⟩

/-- Fields equal one by one are as many as the constructor has. -/
theorem FieldsEqual.length {d : DeclName} {fs : List FieldShape} {ms ms' : List (CTm Head n)}
    (h : FieldsEqual K Γ d fs ms ms') : ms.length = fs.length ∧ ms'.length = fs.length := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ _ ih => exact ⟨congrArg (· + 1) ih.1, congrArg (· + 1) ih.2⟩

theorem FieldsEqual.left {d : DeclName} {fs : List FieldShape} {ms ms' : List (CTm Head n)}
    (h : FieldsEqual K Γ d fs ms ms') : FieldsEqual K Γ d fs ms ms := by
  induction h with
  | nil => exact .nil
  | cons hf e _ ih => exact .cons hf e.left ih

/-- The field of the left list read twice is the field of the left list beside the right
one. -/
theorem FieldAt.left {d : DeclName} {fs : List FieldShape} {ms ms' : List (CTm Head n)} {i : Nat}
    {A m m₂ : CTm Head n} (hl : ms'.length = ms.length) (h : FieldAt K d fs ms ms i A m m₂) :
    m₂ = m ∧ ∃ m', FieldAt K d fs ms ms' i A m m' := by
  obtain ⟨hf, h₁, h₂⟩ := h
  rw [h₁] at h₂
  have hi : i < ms'.length := by
    rw [hl]
    exact (List.getElem?_eq_some_iff.1 h₁).1
  exact ⟨(Option.some.inj h₂).symm, ms'[i], hf, h₁, List.getElem?_eq_getElem hi⟩

/-- Two reductions of one term to applications of a constructor to as many terms as it has
fields reach the same fields. -/
theorem CRedTm.ctor_align {d c : DeclName} {fs : List FieldShape} {M T T' : CTm Head n}
    {ms ms₁ : List (CTm Head n)} (hc : K.ctor d c fs) (hl : ms.length = fs.length)
    (hl₁ : ms₁.length = fs.length) (h : CRedTm H Γ M (CTm.appSpine (.const c) ms) T)
    (h₁ : CRedTm H Γ M (CTm.appSpine (.const c) ms₁) T') : ms₁ = ms :=
  (CTm.appSpine_const_injective
    (CRedTm.nf_unique h₁ h (H.normal_ctor hc hl₁) (H.normal_ctor hc hl))).2

theorem CtorRed.align {d c : DeclName} {fs : List FieldShape} {T M M' : CTm Head n}
    {ms ms' ms₁ ms₁' : List (CTm Head n)} (h : CtorRed H Γ d c fs T M M' ms ms')
    (h₁ : CtorRed H Γ d c fs T M M' ms₁ ms₁') : ms₁ = ms ∧ ms₁' = ms' :=
  ⟨CRedTm.ctor_align h.1 h.2.2.2.2.length.1 h₁.2.2.2.2.length.1 h.2.2.1 h₁.2.2.1,
    CRedTm.ctor_align h.1 h.2.2.2.2.length.2 h₁.2.2.2.2.length.2 h.2.2.2.1 h₁.2.2.2.1⟩

theorem CRedTy.sigma_align {A D D₁ : CTm Head n} {E E₁ : CTm Head (n + 1)}
    (r : CRedTy H Γ A (.sigma D E)) (r₁ : CRedTy H Γ A (.sigma D₁ E₁)) : D₁ = D ∧ E₁ = E := by
  have e := CRedTy.nf_unique r₁ r (H.normal_sigma _ _) (H.normal_sigma _ _)
  injection e with _ h1 h2
  exact ⟨h1, h2⟩

theorem SigmaRed.align {A A' D D' D₁ D₁' : CTm Head n} {E E' E₁ E₁' : CTm Head (n + 1)}
    (hp : SigmaRed H Γ A A' D E D' E')
    (hp₁ : SigmaRed H Γ A A' D₁ E₁ D₁' E₁') : D₁ = D ∧ E₁ = E ∧ D₁' = D' ∧ E₁' = E' := by
  obtain ⟨h1, h2⟩ := CRedTy.sigma_align hp.1 hp₁.1
  obtain ⟨h3, h4⟩ := CRedTy.sigma_align hp.2.1 hp₁.2.1
  exact ⟨h1, h2, h3, h4⟩

/-- A type reduces to at most one ground type. -/
theorem CRedTy.ground_align {A g g₁ : CTm Head n} (hg : K.ground g) (hg₁ : K.ground g₁)
    (r : CRedTy H Γ A g) (r₁ : CRedTy H Γ A g₁) : g₁ = g :=
  CRedTy.nf_unique r₁ r (H.normal_ground hg₁) (H.normal_ground hg)

end Align

/-! ## The canonical forms a token of a kind asserts -/

section Extract

variable {H} {n : Nat} {Γ : CCtx Head n}

theorem RT.ty_pi_shape {s : Tok} (hk : s.kind = .pi) (hn : ent [] s = false)
    {T A A' : CTm Head n} (h : RT H Γ false s T A A') : ∃ D E D' E', PiRed H Γ A A' D E D' E' := by
  cases s with
  | tag k =>
      cases hk
      exact RT.ty_pi_iff.1 h
  | arg k i C d =>
      cases hk
      rcases RT.ty_argPi_iff.1 h with hv | ⟨D, E, D', E', hp, _⟩
      · rw [hv] at hn; cases hn
      · exact ⟨D, E, D', E', hp⟩
  | fn k C Z W =>
      cases hk
      rcases RT.ty_fnPi_iff.1 h with hv | ⟨D, E, D', E', hp, _⟩
      · rw [hv] at hn; cases hn
      · exact ⟨D, E, D', E', hp⟩

theorem RT.ty_ident_shape {s : Tok} (hk : s.kind = .ident) (hn : ent [] s = false)
    {T A A' : CTm Head n} (h : RT H Γ false s T A A') :
    ∃ B x y B' x' y', IdRed H Γ A A' B x y B' x' y' := by
  cases s with
  | tag k =>
      cases hk
      exact RT.ty_ident_iff.1 h
  | arg k i C d =>
      cases hk
      rcases RT.ty_argIdent_iff.1 h with hv | ⟨B, x, y, B', x', y', hi, _⟩
      · rw [hv] at hn; cases hn
      · exact ⟨B, x, y, B', x', y', hi⟩
  | fn k C Z W =>
      cases hk
      rcases RT.ty_fnIdent_iff.1 h with hv | ⟨B, x, y, B', x', y', hi, _⟩
      · rw [hv] at hn; cases hn
      · exact ⟨B, x, y, B', x', y', hi⟩

theorem RT.tm_refl_shape {s : Tok} (hk : s.kind = .refl) (hn : ent [] s = false)
    {T M M' : CTm Head n} (h : RT H Γ true s T M M') :
    ∃ B x y r r', ReflRed H Γ T M M' B x y r r' := by
  cases s with
  | tag k =>
      cases hk
      exact RT.tm_reflTag_iff.1 h
  | arg k i C d =>
      cases hk
      rcases RT.tm_argRefl_iff.1 h with hv | ⟨B, x, y, r, r', hr, _⟩
      · rw [hv] at hn; cases hn
      · exact ⟨B, x, y, r, r', hr⟩
  | fn k C Z W =>
      cases hk
      rcases RT.tm_fnRefl_iff.1 h with hv | ⟨B, x, y, r, r', hr, _⟩
      · rw [hv] at hn; cases hn
      · exact ⟨B, x, y, r, r', hr⟩

theorem RT.tm_succ_shape {s : Tok} (hk : s.kind = .succ) (hn : ent [] s = false)
    {T M M' : CTm Head n} (h : RT H Γ true s T M M') : ∃ m m', SuccRed H Γ T M M' m m' := by
  cases s with
  | tag k =>
      cases hk
      exact RT.tm_succTag_iff.1 h
  | arg k i C d =>
      cases hk
      rcases RT.tm_argSucc_iff.1 h with hv | ⟨m, m', hr, _⟩
      · rw [hv] at hn; cases hn
      · exact ⟨m, m', hr⟩
  | fn k C Z W =>
      cases hk
      rcases RT.tm_fnSucc_iff.1 h with hv | ⟨m, m', hr, _⟩
      · rw [hv] at hn; cases hn
      · exact ⟨m, m', hr⟩

theorem RT.tm_ctor_shape {s : Tok} {d c : DeclName} {fs : List FieldShape}
    (hk : s.kind = .ctor d c fs) (hn : ent [] s = false) {T M M' : CTm Head n}
    (h : RT H Γ true s T M M') : ∃ ms ms', CtorRed H Γ d c fs T M M' ms ms' := by
  cases s with
  | tag k =>
      cases hk
      exact RT.tm_ctorTag_iff.1 h
  | arg k i C r =>
      cases hk
      rcases RT.tm_field_iff.1 h with hv | ⟨ms, ms', hr, _⟩
      · rw [hv] at hn; cases hn
      · exact ⟨ms, ms', hr⟩
  | fn k C Z W =>
      cases hk
      rcases RT.tm_fnCtor_iff.1 h with hv | ⟨ms, ms', hr, _⟩
      · rw [hv] at hn; cases hn
      · exact ⟨ms, ms', hr⟩

theorem RT.ty_data_shape {s : Tok} {d : DeclName} (hk : s.kind = .data d) (hn : ent [] s = false)
    {T A A' : CTm Head n} (h : RT H Γ false s T A A') : DataRed H Γ d A A' := by
  cases s with
  | tag k =>
      cases hk
      exact RT.ty_data_iff.1 h
  | arg k i C r =>
      cases hk
      rcases RT.ty_param_iff.1 h with hv | ⟨hd, _⟩
      · rw [hv] at hn; cases hn
      · exact hd
  | fn k C Z W =>
      cases hk
      rcases RT.ty_fnData_iff.1 h with hv | ⟨hd, _⟩
      · rw [hv] at hn; cases hn
      · exact hd

theorem RT.ty_sigma_shape {s : Tok} (hk : s.kind = .sigma) (hn : ent [] s = false)
    {T A A' : CTm Head n} (h : RT H Γ false s T A A') :
    ∃ D E D' E', SigmaRed H Γ A A' D E D' E' := by
  cases s with
  | tag k =>
      cases hk
      exact RT.ty_sigma_iff.1 h
  | arg k i C d =>
      cases hk
      rcases RT.ty_argSigma_iff.1 h with hv | ⟨D, E, D', E', hp, _⟩
      · rw [hv] at hn; cases hn
      · exact ⟨D, E, D', E', hp⟩
  | fn k C Z W =>
      cases hk
      rcases RT.ty_fnSigma_iff.1 h with hv | ⟨D, E, D', E', hp, _⟩
      · rw [hv] at hn; cases hn
      · exact ⟨D, E, D', E', hp⟩

/-- Every token of kind `pair` not entailed by the empty list asserts that the first
projections are equal at the domain of a dependent pair type the type reduces to. -/
theorem RT.tm_pair_core {s : Tok} (hk : s.kind = .pair) (hn : ent [] s = false)
    {T M M' : CTm Head n} (h : RT H Γ true s T M M') :
    ∀ D E, CRedTy H Γ T (.sigma D E) → CEqual P Γ (.fst M) (.fst M') D := by
  intro D E hT
  cases s with
  | tag k =>
      cases hk
      exact RT.tm_pairTag_iff.1 h D E hT
  | arg k i C d =>
      cases hk
      rcases RT.tm_argPair_iff.1 h with hv | hcl
      · rw [hv] at hn; cases hn
      · exact (hcl D E hT).1
  | fn k C Z W =>
      cases hk
      rcases RT.tm_fnPair_iff.1 h with hv | hcl
      · rw [hv] at hn; cases hn
      · exact (hcl D E hT).1

end Extract

/-! ## The components the tokens of one kind relate -/

section Components

variable {H} {n : Nat} {Γ : CCtx Head n}

/-- The domain tokens of the tokens of kind `pi` of a list relate the domains. -/
theorem RT.pi_dom {v : List Tok} {T A A' D D' : CTm Head n} {E E' : CTm Head (n + 1)}
    (hp : PiRed H Γ A A' D E D' E') (hv : ∀ s ∈ v, s.kind = .pi → RT H Γ false s T A A') :
    ∀ r ∈ args .pi 0 v, RT H Γ false r D D D' := by
  intro r hr
  rcases mem_args_iff.1 hr with ⟨C, hC⟩ | ⟨-, s, hs, hk, hd⟩
  · rcases RT.ty_argPi_iff.1 (hv _ hC rfl) with hvac | ⟨D₁, E₁, D₁', E₁', hp₁, -, hr₁⟩
    · exact RT.of_vacuous (vacuous_arg hvac)
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hp.align hp₁
      exact hr₁ rfl
  · cases s with
    | tag k => cases hd
    | arg k i C d =>
        cases hk
        rcases RT.ty_argPi_iff.1 (hv _ hs rfl) with hvac | ⟨D₁, E₁, D₁', E₁', hp₁, hC₁, -⟩
        · exact RT.of_vacuous (vacuous_dep hvac hd)
        · obtain ⟨rfl, rfl, rfl, rfl⟩ := hp.align hp₁
          exact hC₁ r hd
    | fn k C Z W =>
        cases hk
        rcases RT.ty_fnPi_iff.1 (hv _ hs rfl) with hvac | ⟨D₁, E₁, D₁', E₁', hp₁, hC₁, -⟩
        · exact RT.of_vacuous (vacuous_dep hvac hd)
        · obtain ⟨rfl, rfl, rfl, rfl⟩ := hp.align hp₁
          exact hC₁ r hd

/-- A family entry of kind `pi` of a list relates the families, or observes
nothing. -/
theorem RT.pi_fam {v : List Tok} {T A A' D D' : CTm Head n} {E E' : CTm Head (n + 1)}
    (hp : PiRed H Γ A A' D E D' E') (hv : ∀ s ∈ v, s.kind = .pi → RT H Γ false s T A A')
    {C Z W : List Tok} (hm : Tok.fn .pi C Z W ∈ v) :
    ent [] (.fn .pi C Z W) = true ∨
      ((∀ N N', CEqual P Γ N N' D → (∀ z ∈ Z, RT H Γ true z D N N') →
          ∀ w ∈ W, RT H Γ false w (CTm.inst0 N E) (CTm.inst0 N E) (CTm.inst0 N' E) ∧
            RT H Γ false w (CTm.inst0 N E') (CTm.inst0 N E') (CTm.inst0 N' E')) ∧
        (∀ N, CTyped P Γ N D → (∀ z ∈ Z, RT H Γ true z D N N) →
          ∀ w ∈ W, RT H Γ false w (CTm.inst0 N E) (CTm.inst0 N E) (CTm.inst0 N E'))) := by
  rcases RT.ty_fnPi_iff.1 (hv _ hm rfl) with hvac | ⟨D₁, E₁, D₁', E₁', hp₁, -, hf₁, hg₁⟩
  · exact .inl hvac
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hp.align hp₁
    exact .inr ⟨hf₁, hg₁⟩

/-- The carrier tokens of the tokens of kind `ident` of a list relate the carriers. -/
theorem RT.ident_carrier {v : List Tok} {T A A' B x y B' x' y' : CTm Head n}
    (hi : IdRed H Γ A A' B x y B' x' y') (hv : ∀ s ∈ v, s.kind = .ident → RT H Γ false s T A A') :
    ∀ r ∈ args .ident 0 v, RT H Γ false r B B B' := by
  intro r hr
  rcases mem_args_iff.1 hr with ⟨C, hC⟩ | ⟨-, s, hs, hk, hd⟩
  · rcases RT.ty_argIdent_iff.1 (hv _ hC rfl) with hvac |
      ⟨B₁, x₁, y₁, B₁', x₁', y₁', hi₁, -, hr₁, -, -⟩
    · exact RT.of_vacuous (vacuous_arg hvac)
    · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi.align hi₁
      exact hr₁ rfl
  · cases s with
    | tag k => cases hd
    | arg k i C d =>
        cases hk
        rcases RT.ty_argIdent_iff.1 (hv _ hs rfl) with hvac |
          ⟨B₁, x₁, y₁, B₁', x₁', y₁', hi₁, hC₁, -, -, -⟩
        · exact RT.of_vacuous (vacuous_dep hvac hd)
        · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi.align hi₁
          exact hC₁ r hd
    | fn k C Z W =>
        cases hk
        rcases RT.ty_fnIdent_iff.1 (hv _ hs rfl) with hvac |
          ⟨B₁, x₁, y₁, B₁', x₁', y₁', hi₁, hC₁⟩
        · exact RT.of_vacuous (vacuous_dep hvac hd)
        · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi.align hi₁
          exact hC₁ r hd

/-- The endpoint tokens of the tokens of kind `ident` of a list relate the
endpoints. -/
theorem RT.ident_ends {v : List Tok} {T A A' B x y B' x' y' : CTm Head n}
    (hi : IdRed H Γ A A' B x y B' x' y') (hv : ∀ s ∈ v, s.kind = .ident → RT H Γ false s T A A') :
    (∀ r ∈ args .ident 1 v, RT H Γ true r B x x') ∧
      ∀ r ∈ args .ident 2 v, RT H Γ true r B y y' := by
  constructor
  · intro r hr
    rcases mem_args_iff.1 hr with ⟨C, hC⟩ | ⟨h1, -⟩
    · rcases RT.ty_argIdent_iff.1 (hv _ hC rfl) with hvac |
        ⟨B₁, x₁, y₁, B₁', x₁', y₁', hi₁, -, -, hr₁, -⟩
      · exact RT.of_vacuous (vacuous_arg hvac)
      · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi.align hi₁
        exact hr₁ rfl
    · cases h1
  · intro r hr
    rcases mem_args_iff.1 hr with ⟨C, hC⟩ | ⟨h2, -⟩
    · rcases RT.ty_argIdent_iff.1 (hv _ hC rfl) with hvac |
        ⟨B₁, x₁, y₁, B₁', x₁', y₁', hi₁, -, -, -, hr₁⟩
      · exact RT.of_vacuous (vacuous_arg hvac)
      · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hi.align hi₁
        exact hr₁ rfl
    · cases h2

/-- The point tokens of the tokens of kind `refl` of a list relate the points and
the endpoints. -/
theorem RT.refl_points {v : List Tok} {T M M' B x y r r' : CTm Head n}
    (hr : ReflRed H Γ T M M' B x y r r') (hv : ∀ s ∈ v, s.kind = .refl → RT H Γ true s T M M') :
    ∀ c ∈ args .refl 0 v, RT H Γ true c B r x ∧ RT H Γ true c B r y ∧ RT H Γ true c B r r' := by
  intro c hc
  rcases mem_args_iff.1 hc with ⟨C, hC⟩ | ⟨-, s, hs, hk, hd⟩
  · rcases RT.tm_argRefl_iff.1 (hv _ hC rfl) with hvac | ⟨B₁, x₁, y₁, r₁, r₁', hr₁, -, hc₁⟩
    · exact ⟨RT.of_vacuous (vacuous_arg hvac), RT.of_vacuous (vacuous_arg hvac),
        RT.of_vacuous (vacuous_arg hvac)⟩
    · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hr.align hr₁
      exact hc₁ rfl
  · cases s with
    | tag k => cases hd
    | arg k i C d =>
        cases hk
        rcases RT.tm_argRefl_iff.1 (hv _ hs rfl) with hvac | ⟨B₁, x₁, y₁, r₁, r₁', hr₁, hC₁, -⟩
        · exact ⟨RT.of_vacuous (vacuous_dep hvac hd), RT.of_vacuous (vacuous_dep hvac hd),
            RT.of_vacuous (vacuous_dep hvac hd)⟩
        · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hr.align hr₁
          exact hC₁ c hd
    | fn k C Z W =>
        cases hk
        rcases RT.tm_fnRefl_iff.1 (hv _ hs rfl) with hvac | ⟨B₁, x₁, y₁, r₁, r₁', hr₁, hC₁⟩
        · exact ⟨RT.of_vacuous (vacuous_dep hvac hd), RT.of_vacuous (vacuous_dep hvac hd),
            RT.of_vacuous (vacuous_dep hvac hd)⟩
        · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hr.align hr₁
          exact hC₁ c hd

/-- The predecessor tokens of the tokens of kind `succ` of a list relate the
predecessors. -/
theorem RT.succ_pred {v : List Tok} {T M M' m m' : CTm Head n}
    (hs : SuccRed H Γ T M M' m m') (hv : ∀ s ∈ v, s.kind = .succ → RT H Γ true s T M M') :
    ∀ c ∈ args .succ 0 v, RT H Γ true c (.const K.num) m m' := by
  intro c hc
  rcases mem_args_iff.1 hc with ⟨C, hC⟩ | ⟨-, s, hs', hk, hd⟩
  · rcases RT.tm_argSucc_iff.1 (hv _ hC rfl) with hvac | ⟨m₁, m₁', hs₁, -, hc₁⟩
    · exact RT.of_vacuous (vacuous_arg hvac)
    · obtain ⟨rfl, rfl⟩ := hs.align hs₁
      exact hc₁ rfl
  · cases s with
    | tag k => cases hd
    | arg k i C d =>
        cases hk
        rcases RT.tm_argSucc_iff.1 (hv _ hs' rfl) with hvac | ⟨m₁, m₁', hs₁, hC₁, -⟩
        · exact RT.of_vacuous (vacuous_dep hvac hd)
        · obtain ⟨rfl, rfl⟩ := hs.align hs₁
          exact hC₁ c hd
    | fn k C Z W =>
        cases hk
        rcases RT.tm_fnSucc_iff.1 (hv _ hs' rfl) with hvac | ⟨m₁, m₁', hs₁, hC₁⟩
        · exact RT.of_vacuous (vacuous_dep hvac hd)
        · obtain ⟨rfl, rfl⟩ := hs.align hs₁
          exact hC₁ c hd

/-- The field tokens `i` of the tokens of a constructor kind of a list relate the fields
`i`. -/
theorem RT.ctor_fields {v : List Tok} {d c : DeclName} {fs : List FieldShape}
    {T M M' : CTm Head n} {ms ms' : List (CTm Head n)} (hs : CtorRed H Γ d c fs T M M' ms ms')
    (hv : ∀ s ∈ v, s.kind = .ctor d c fs → RT H Γ true s T M M') (i : Nat) :
    ∀ r ∈ args (.ctor d c fs) i v, ∀ A m m', FieldAt K d fs ms ms' i A m m' →
      RT H Γ true r A m m' := by
  intro r hr
  rcases mem_args_iff.1 hr with ⟨C, hC⟩ | ⟨rfl, s, hs', hk, hd⟩
  · rcases RT.tm_field_iff.1 (hv _ hC rfl) with hvac | ⟨ms₁, ms₁', hs₁, -, hr₁⟩
    · exact fun _ _ _ _ => RT.of_vacuous (vacuous_arg hvac)
    · obtain ⟨rfl, rfl⟩ := hs.align hs₁
      exact hr₁
  · cases s with
    | tag k => cases hd
    | arg k j C q =>
        cases hk
        rcases RT.tm_field_iff.1 (hv _ hs' rfl) with hvac | ⟨ms₁, ms₁', hs₁, hC₁, -⟩
        · exact fun _ _ _ _ => RT.of_vacuous (vacuous_dep hvac hd)
        · obtain ⟨rfl, rfl⟩ := hs.align hs₁
          exact hC₁ r hd
    | fn k C Z W =>
        cases hk
        rcases RT.tm_fnCtor_iff.1 (hv _ hs' rfl) with hvac | ⟨ms₁, ms₁', hs₁, hC₁⟩
        · exact fun _ _ _ _ => RT.of_vacuous (vacuous_dep hvac hd)
        · obtain ⟨rfl, rfl⟩ := hs.align hs₁
          exact hC₁ r hd

/-- The parameter tokens `i` of the tokens of a datatype kind of a list relate the parameter
`i` of the datatype to itself. -/
theorem RT.data_params {v : List Tok} {d : DeclName} {T A A' : CTm Head n}
    (hv : ∀ s ∈ v, s.kind = .data d → RT H Γ false s T A A') (i : Nat) :
    ∀ r ∈ args (.data d) i v, ∀ B, K.param d i = some B → RT H Γ false r B B B := by
  intro r hr
  rcases mem_args_iff.1 hr with ⟨C, hC⟩ | ⟨rfl, s, hs, hk, hd⟩
  · rcases RT.ty_param_iff.1 (hv _ hC rfl) with hvac | ⟨-, -, hr₁⟩
    · exact fun _ _ => RT.of_vacuous (vacuous_arg hvac)
    · exact hr₁
  · cases s with
    | tag k => cases hd
    | arg k j C q =>
        cases hk
        rcases RT.ty_param_iff.1 (hv _ hs rfl) with hvac | ⟨-, hC₁, -⟩
        · exact fun _ _ => RT.of_vacuous (vacuous_dep hvac hd)
        · exact hC₁ r hd
    | fn k C Z W =>
        cases hk
        rcases RT.ty_fnData_iff.1 (hv _ hs rfl) with hvac | ⟨-, hC₁⟩
        · exact fun _ _ => RT.of_vacuous (vacuous_dep hvac hd)
        · exact hC₁ r hd

/-- The domain tokens of the tokens of kind `sigma` of a list relate the domains. -/
theorem RT.sigma_dom {v : List Tok} {T A A' D D' : CTm Head n} {E E' : CTm Head (n + 1)}
    (hp : SigmaRed H Γ A A' D E D' E') (hv : ∀ s ∈ v, s.kind = .sigma → RT H Γ false s T A A') :
    ∀ r ∈ args .sigma 0 v, RT H Γ false r D D D' := by
  intro r hr
  rcases mem_args_iff.1 hr with ⟨C, hC⟩ | ⟨-, s, hs, hk, hd⟩
  · rcases RT.ty_argSigma_iff.1 (hv _ hC rfl) with hvac | ⟨D₁, E₁, D₁', E₁', hp₁, -, hr₁⟩
    · exact RT.of_vacuous (vacuous_arg hvac)
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hp.align hp₁
      exact hr₁ rfl
  · cases s with
    | tag k => cases hd
    | arg k i C d =>
        cases hk
        rcases RT.ty_argSigma_iff.1 (hv _ hs rfl) with hvac | ⟨D₁, E₁, D₁', E₁', hp₁, hC₁, -⟩
        · exact RT.of_vacuous (vacuous_dep hvac hd)
        · obtain ⟨rfl, rfl, rfl, rfl⟩ := hp.align hp₁
          exact hC₁ r hd
    | fn k C Z W =>
        cases hk
        rcases RT.ty_fnSigma_iff.1 (hv _ hs rfl) with hvac | ⟨D₁, E₁, D₁', E₁', hp₁, hC₁, -⟩
        · exact RT.of_vacuous (vacuous_dep hvac hd)
        · obtain ⟨rfl, rfl, rfl, rfl⟩ := hp.align hp₁
          exact hC₁ r hd

/-- A family entry of kind `sigma` of a list relates the families, or observes
nothing. -/
theorem RT.sigma_fam {v : List Tok} {T A A' D D' : CTm Head n} {E E' : CTm Head (n + 1)}
    (hp : SigmaRed H Γ A A' D E D' E') (hv : ∀ s ∈ v, s.kind = .sigma → RT H Γ false s T A A')
    {C Z W : List Tok} (hm : Tok.fn .sigma C Z W ∈ v) :
    ent [] (.fn .sigma C Z W) = true ∨
      ((∀ N N', CEqual P Γ N N' D → (∀ z ∈ Z, RT H Γ true z D N N') →
          ∀ w ∈ W, RT H Γ false w (CTm.inst0 N E) (CTm.inst0 N E) (CTm.inst0 N' E) ∧
            RT H Γ false w (CTm.inst0 N E') (CTm.inst0 N E') (CTm.inst0 N' E')) ∧
        (∀ N, CTyped P Γ N D → (∀ z ∈ Z, RT H Γ true z D N N) →
          ∀ w ∈ W, RT H Γ false w (CTm.inst0 N E) (CTm.inst0 N E) (CTm.inst0 N E'))) := by
  rcases RT.ty_fnSigma_iff.1 (hv _ hm rfl) with hvac | ⟨D₁, E₁, D₁', E₁', hp₁, -, hf₁, hg₁⟩
  · exact .inl hvac
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hp.align hp₁
    exact .inr ⟨hf₁, hg₁⟩

/-- The first-component tokens of the tokens of kind `pair` of a list relate the
first projections. -/
theorem RT.pair_first {v : List Tok} {T M M' D : CTm Head n} {E : CTm Head (n + 1)}
    (hT : CRedTy H Γ T (.sigma D E)) (hv : ∀ s ∈ v, s.kind = .pair → RT H Γ true s T M M') :
    ∀ r ∈ args .pair 0 v, RT H Γ true r D (.fst M) (.fst M') := by
  intro r hr
  rcases mem_args_iff.1 hr with ⟨C, hC⟩ | ⟨-, s, hs, hk, hd⟩
  · rcases RT.tm_argPair_iff.1 (hv _ hC rfl) with hvac | hcl
    · exact RT.of_vacuous (vacuous_arg hvac)
    · exact (hcl D E hT).2.2.1 rfl
  · cases s with
    | tag k => cases hd
    | arg k i C d =>
        cases hk
        rcases RT.tm_argPair_iff.1 (hv _ hs rfl) with hvac | hcl
        · exact RT.of_vacuous (vacuous_dep hvac hd)
        · exact (hcl D E hT).2.1 r hd
    | fn k C Z W =>
        cases hk
        rcases RT.tm_fnPair_iff.1 (hv _ hs rfl) with hvac | hcl
        · exact RT.of_vacuous (vacuous_dep hvac hd)
        · exact (hcl D E hT).2 r hd

/-- The second-component tokens of the tokens of kind `pair` of a list relate the
second projections, at the family's value at every term with a common reduct with
the left first projection. -/
theorem RT.pair_second {v : List Tok} {T M M' D : CTm Head n} {E : CTm Head (n + 1)}
    (hT : CRedTy H Γ T (.sigma D E)) (hv : ∀ s ∈ v, s.kind = .pair → RT H Γ true s T M M') :
    ∀ r ∈ args .pair 1 v, ∀ N Q, CRedTm H Γ (.fst M) Q D → CRedTm H Γ N Q D →
      RT H Γ true r (CTm.inst0 N E) (.snd M) (.snd M') := by
  intro r hr N Q hQ hNQ
  rcases mem_args_iff.1 hr with ⟨C, hC⟩ | ⟨h1, -⟩
  · rcases RT.tm_argPair_iff.1 (hv _ hC rfl) with hvac | hcl
    · exact RT.of_vacuous (vacuous_arg hvac)
    · exact (hcl D E hT).2.2.2 rfl N Q hQ hNQ
  · cases h1

end Components

/-! ## Closure under entailment -/

section Closure

variable {H} {n : Nat} {Γ : CCtx Head n}

theorem kind_cases_ty (k : Kind) :
    k = .pi ∨ k = .ident ∨ (∃ d, k = .data d) ∨ (k ≠ .pi ∧ k ≠ .ident ∧ ∀ d, k ≠ .data d) := by
  cases k <;> simp

theorem kind_cases_tm (k : Kind) :
    k = .lam ∨ k = .refl ∨ k = .succ ∨ (∃ d c fs, k = .ctor d c fs) ∨
      (k ≠ .lam ∧ k ≠ .refl ∧ k ≠ .succ ∧ ∀ d c fs, k ≠ .ctor d c fs) := by
  cases k <;> simp

theorem kind_cases_tySigma (k : Kind) :
    k = .pi ∨ k = .ident ∨ k = .sigma ∨ (∃ d, k = .data d) ∨
      (k ≠ .pi ∧ k ≠ .ident ∧ k ≠ .sigma ∧ ∀ d, k ≠ .data d) := by
  cases k <;> simp

theorem kind_cases_tmPair (k : Kind) :
    k = .lam ∨ k = .refl ∨ k = .succ ∨ k = .pair ∨ (∃ d c fs, k = .ctor d c fs) ∨
      (k ≠ .lam ∧ k ≠ .refl ∧ k ≠ .succ ∧ k ≠ .pair ∧ ∀ d c fs, k ≠ .ctor d c fs) := by
  cases k <;> simp

theorem RT.closed_aux : ∀ (N : Nat) (b : Bool) (v : List Tok) (t : Tok) (T x x' : CTm Head n),
    2 * (Tok.depthL v + t.depth) + b.toNat < N → ent v t = true →
      (∀ s ∈ v, s.kind = t.kind → RT H Γ b s T x x') → RT H Γ b t T x x'
  | 0, _, _, _, _, _, _, hN, _, _ => absurd hN (Nat.not_lt_zero _)
  | N + 1, b, v, t, T, x, x', hN, e, h => by
    have IH := RT.closed_aux N
    cases hv : ent [] t with
    | true => exact RT.of_vacuous hv
    | false =>
    obtain ⟨s₀, hs₀, hk₀, hn₀⟩ := source_of_ent e hv
    -- A tag is entailed only by itself.
    cases t with
    | tag k =>
        rw [ent_tag, hasTag_iff] at e
        exact h _ e rfl
    | arg k i C d =>
        cases b with
        | false =>
            simp only [Bool.toNat_false, Nat.add_zero] at hN
            rw [ent_arg, Bool.and_eq_true, List.all_eq_true] at e
            rcases kind_cases_tySigma k with rfl | rfl | rfl | hk | hk
            · obtain ⟨D, E, D', E', hp⟩ := RT.ty_pi_shape hk₀ hn₀ (h s₀ hs₀ hk₀)
              have hdom := RT.pi_dom hp (fun s hs hk => h s hs hk)
              refine RT.ty_argPi_iff.2 (.inr ⟨D, E, D', E', hp, fun c hc => ?_, fun hi => ?_⟩)
              · refine IH false (args .pi 0 v) c D D D' ?_ (e.1 c hc) (fun r hr _ => hdom r hr)
                have := depthL_args .pi 0 v
                have := Tok.depth_lt_of_mem_dep (t := .arg .pi i C d) hc
                simp only [Bool.toNat_false]; omega
              · subst hi
                refine IH false (args .pi 0 v) d D D D' ?_ e.2 (fun r hr _ => hdom r hr)
                have := depthL_args .pi 0 v
                have := depth_lt_arg .pi 0 C d
                simp only [Bool.toNat_false]; omega
            · obtain ⟨B, y₁, y₂, B', y₁', y₂', hi⟩ := RT.ty_ident_shape hk₀ hn₀ (h s₀ hs₀ hk₀)
              have hcar := RT.ident_carrier hi (fun s hs hk => h s hs hk)
              have hends := RT.ident_ends hi (fun s hs hk => h s hs hk)
              refine RT.ty_argIdent_iff.2 (.inr ⟨B, y₁, y₂, B', y₁', y₂', hi, fun c hc => ?_,
                fun hi0 => ?_, fun hi1 => ?_, fun hi2 => ?_⟩)
              · refine IH false (args .ident 0 v) c B B B' ?_ (e.1 c hc) (fun r hr _ => hcar r hr)
                have := depthL_args .ident 0 v
                have := Tok.depth_lt_of_mem_dep (t := .arg .ident i C d) hc
                simp only [Bool.toNat_false]; omega
              · subst hi0
                refine IH false (args .ident 0 v) d B B B' ?_ e.2 (fun r hr _ => hcar r hr)
                have := depthL_args .ident 0 v
                have := depth_lt_arg .ident 0 C d
                simp only [Bool.toNat_false]; omega
              · subst hi1
                refine IH true (args .ident 1 v) d B y₁ y₁' ?_ e.2 (fun r hr _ => hends.1 r hr)
                have := depthL_args .ident 1 v
                have := depth_lt_arg .ident 1 C d
                simp only [Bool.toNat_true]; omega
              · subst hi2
                refine IH true (args .ident 2 v) d B y₂ y₂' ?_ e.2 (fun r hr _ => hends.2 r hr)
                have := depthL_args .ident 2 v
                have := depth_lt_arg .ident 2 C d
                simp only [Bool.toNat_true]; omega
            · obtain ⟨D, E, D', E', hp⟩ := RT.ty_sigma_shape hk₀ hn₀ (h s₀ hs₀ hk₀)
              have hdom := RT.sigma_dom hp (fun s hs hk => h s hs hk)
              refine RT.ty_argSigma_iff.2 (.inr ⟨D, E, D', E', hp, fun c hc => ?_, fun hi => ?_⟩)
              · refine IH false (args .sigma 0 v) c D D D' ?_ (e.1 c hc) (fun r hr _ => hdom r hr)
                have := depthL_args .sigma 0 v
                have := Tok.depth_lt_of_mem_dep (t := .arg .sigma i C d) hc
                simp only [Bool.toNat_false]; omega
              · subst hi
                refine IH false (args .sigma 0 v) d D D D' ?_ e.2 (fun r hr _ => hdom r hr)
                have := depthL_args .sigma 0 v
                have := depth_lt_arg .sigma 0 C d
                simp only [Bool.toNat_false]; omega
            · obtain ⟨dn, rfl⟩ := hk
              have hpar := RT.data_params (fun s hs hk => h s hs hk)
              refine RT.ty_param_iff.2 (.inr ⟨RT.ty_data_shape hk₀ hn₀ (h s₀ hs₀ hk₀),
                fun c hc B hB => ?_, fun B hB => ?_⟩)
              · refine IH false (args (.data dn) 0 v) c B B B ?_ (e.1 c hc)
                  (fun r hr _ => hpar 0 r hr B hB)
                have := depthL_args (.data dn) 0 v
                have := Tok.depth_lt_of_mem_dep (t := .arg (.data dn) i C d) hc
                simp only [Bool.toNat_false]; omega
              · refine IH false (args (.data dn) i v) d B B B ?_ e.2
                  (fun r hr _ => hpar i r hr B hB)
                have := depthL_args (.data dn) i v
                have := depth_lt_arg (.data dn) i C d
                simp only [Bool.toNat_false]; omega
            · exact RT.ty_arg_other hk
        | true =>
            simp only [Bool.toNat_true] at hN
            rw [ent_arg, Bool.and_eq_true, List.all_eq_true] at e
            cases htk : typeKind k with
            | true =>
                have htk' : typeKind (Tok.arg k i C d).kind = true := htk
                have htk₀ : typeKind s₀.kind = true := by rw [hk₀]; exact htk'
                have hstep : ∀ {s}, s ∈ v → s.kind = (Tok.arg k i C d).kind →
                    ∀ {h₀ : Head}, CRedTy H Γ T (.head h₀) → RT H Γ false s x x x' := by
                  intro s hs hk h₀ hred
                  have hts : typeKind s.kind = true := by rw [hk]; exact htk'
                  rcases (RT.tm_type_iff hts).1 (h s hs hk) with hvac | ⟨_, _, _, hr⟩ | ⟨hp, _⟩
                  · exact RT.of_vacuous hvac
                  · exact hr
                  · exact (CRedTy.head_ne_prop hred hp).elim
                have hstep' : ∀ {s}, s ∈ v → s.kind = (Tok.arg k i C d).kind →
                    CRedTy H Γ T (.const K.prop) →
                      RT H Γ false s (.app (.const K.holds) x) (.app (.const K.holds) x)
                        (.app (.const K.holds) x') := by
                  intro s hs hk hprop
                  have hts : typeKind s.kind = true := by rw [hk]; exact htk'
                  rcases (RT.tm_type_iff hts).1 (h s hs hk) with hvac | ⟨_, _, hred, _⟩ | ⟨_, hr⟩
                  · exact RT.of_vacuous hvac
                  · exact (CRedTy.head_ne_prop hred hprop).elim
                  · exact hr
                have e' : ent v (.arg k i C d) = true := by
                  rw [ent_arg, Bool.and_eq_true, List.all_eq_true]; exact e
                rcases (RT.tm_type_iff htk₀).1 (h s₀ hs₀ hk₀) with hvac | ⟨h₀, hu₀, hred, _⟩ |
                  ⟨hp, _⟩
                · rw [hvac] at hn₀; cases hn₀
                · refine (RT.tm_type_iff htk').2 (.inr (.inl ⟨h₀, hu₀, hred, ?_⟩))
                  exact IH false v _ x x x' (by simp only [Bool.toNat_false]; omega) e'
                    (fun s hs hk => hstep hs hk hred)
                · refine (RT.tm_type_iff htk').2 (.inr (.inr ⟨hp, ?_⟩))
                  exact IH false v _ _ _ _ (by simp only [Bool.toNat_false]; omega) e'
                    (fun s hs hk => hstep' hs hk hp)
            | false =>
                rcases kind_cases_tmPair k with rfl | rfl | rfl | rfl | hk | hk
                · exact RT.tm_other htk (fun _ _ _ e => nomatch e) (by intro e; cases e)
                    (fun e => nomatch e) (by intro e; cases e) (by intro e; cases e)
                    (fun _ _ _ e => nomatch e)
                · obtain ⟨B, y₁, y₂, r, r', hr⟩ := RT.tm_refl_shape hk₀ hn₀ (h s₀ hs₀ hk₀)
                  have hpts := RT.refl_points hr (fun s hs hk => h s hs hk)
                  have go : ∀ c, ent (args .refl 0 v) c = true → c.depth < (Tok.arg .refl i C d).depth →
                      RT H Γ true c B r y₁ ∧ RT H Γ true c B r y₂ ∧ RT H Γ true c B r r' := by
                    intro c hc hlt
                    have := depthL_args .refl 0 v
                    refine ⟨IH true (args .refl 0 v) c B r y₁ ?_ hc (fun q hq _ => (hpts q hq).1),
                      IH true (args .refl 0 v) c B r y₂ ?_ hc (fun q hq _ => (hpts q hq).2.1),
                      IH true (args .refl 0 v) c B r r' ?_ hc (fun q hq _ => (hpts q hq).2.2)⟩ <;>
                    · simp only [Bool.toNat_true]; omega
                  refine RT.tm_argRefl_iff.2 (.inr ⟨B, y₁, y₂, r, r', hr, fun c hc => ?_, fun hi => ?_⟩)
                  · exact go c (e.1 c hc) (Tok.depth_lt_of_mem_dep (t := .arg .refl i C d) hc)
                  · subst hi; exact go d e.2 (depth_lt_arg .refl 0 C d)
                · obtain ⟨m, m', hs⟩ := RT.tm_succ_shape hk₀ hn₀ (h s₀ hs₀ hk₀)
                  have hpred := RT.succ_pred hs (fun s hs hk => h s hs hk)
                  have go : ∀ c, ent (args .succ 0 v) c = true → c.depth < (Tok.arg .succ i C d).depth →
                      RT H Γ true c (.const K.num) m m' := by
                    intro c hc hlt
                    have := depthL_args .succ 0 v
                    exact IH true (args .succ 0 v) c _ m m' (by simp only [Bool.toNat_true]; omega) hc
                      (fun q hq _ => hpred q hq)
                  refine RT.tm_argSucc_iff.2 (.inr ⟨m, m', hs, fun c hc => ?_, fun hi => ?_⟩)
                  · exact go c (e.1 c hc) (Tok.depth_lt_of_mem_dep (t := .arg .succ i C d) hc)
                  · subst hi; exact go d e.2 (depth_lt_arg .succ 0 C d)
                · refine RT.tm_argPair_iff.2 (.inr fun D E hT => ?_)
                  have hfirst := RT.pair_first hT (fun s hs hk => h s hs hk)
                  have hsecond := RT.pair_second hT (fun s hs hk => h s hs hk)
                  refine ⟨RT.tm_pair_core hk₀ hn₀ (h s₀ hs₀ hk₀) D E hT, fun c hc => ?_,
                    fun hi => ?_, fun hi N Q hQ hNQ => ?_⟩
                  · refine IH true (args .pair 0 v) c _ _ _ ?_ (e.1 c hc) (fun r hr _ => hfirst r hr)
                    have := depthL_args .pair 0 v
                    have := Tok.depth_lt_of_mem_dep (t := .arg .pair i C d) hc
                    simp only [Bool.toNat_true]; omega
                  · subst hi
                    refine IH true (args .pair 0 v) d _ _ _ ?_ e.2 (fun r hr _ => hfirst r hr)
                    have := depthL_args .pair 0 v
                    have := depth_lt_arg .pair 0 C d
                    simp only [Bool.toNat_true]; omega
                  · subst hi
                    refine IH true (args .pair 1 v) d _ _ _ ?_ e.2
                      (fun r hr _ => hsecond r hr N Q hQ hNQ)
                    have := depthL_args .pair 1 v
                    have := depth_lt_arg .pair 1 C d
                    simp only [Bool.toNat_true]; omega
                · obtain ⟨dn, cn, fs, rfl⟩ := hk
                  obtain ⟨ms, ms', hs⟩ := RT.tm_ctor_shape hk₀ hn₀ (h s₀ hs₀ hk₀)
                  have hfld := RT.ctor_fields hs (fun s hs hk => h s hs hk)
                  refine RT.tm_field_iff.2 (.inr ⟨ms, ms', hs, fun c hc A m m' hA => ?_,
                    fun A m m' hA => ?_⟩)
                  · refine IH true (args (.ctor dn cn fs) 0 v) c A m m' ?_ (e.1 c hc)
                      (fun r hr _ => hfld 0 r hr A m m' hA)
                    have := depthL_args (.ctor dn cn fs) 0 v
                    have := Tok.depth_lt_of_mem_dep (t := .arg (.ctor dn cn fs) i C d) hc
                    simp only [Bool.toNat_true]; omega
                  · refine IH true (args (.ctor dn cn fs) i v) d A m m' ?_ e.2
                      (fun r hr _ => hfld i r hr A m m' hA)
                    have := depthL_args (.ctor dn cn fs) i v
                    have := depth_lt_arg (.ctor dn cn fs) i C d
                    simp only [Bool.toNat_true]; omega
                · exact RT.tm_other htk (fun _ _ _ e => nomatch e) hk.2.1
                    (fun e => nomatch e) hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2
    | fn k C Z W =>
        cases b with
        | false =>
            simp only [Bool.toNat_false, Nat.add_zero] at hN
            rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at e
            rcases kind_cases_tySigma k with rfl | rfl | rfl | hk | hk
            · obtain ⟨D, E, D', E', hp⟩ := RT.ty_pi_shape hk₀ hn₀ (h s₀ hs₀ hk₀)
              have hv' : ∀ s ∈ v, s.kind = .pi → RT H Γ false s T x x' := fun s hs hk => h s hs hk
              have hdom := RT.pi_dom hp hv'
              -- related arguments below the input are related below the input of an entry
              have hargs : ∀ {N₁ N₁'}, (∀ z ∈ Z, RT H Γ true z D N₁ N₁') →
                  ∀ {C' Z' W'}, Tok.fn .pi C' Z' W' ∈ v → (∀ z ∈ Z', ent Z z = true) →
                    ∀ z ∈ Z', RT H Γ true z D N₁ N₁' := by
                intro N₁ N₁' hZ C' Z' W' hm hZ' z hz
                refine IH true Z z D N₁ N₁' ?_ (hZ' z hz) (fun q hq _ => hZ q hq)
                have := depthL_lt_fn_left .pi C Z W
                have := depth_lt_fn_left (k := .pi) (C := C') (Y := W') hz
                have := Tok.depth_le_of_mem hm
                simp only [Bool.toNat_true]; omega
              have hout : ∀ w, w ∈ W → ∀ {A₁ A₂ : CTm Head n},
                  (∀ r ∈ fnApp .pi v Z, RT H Γ false r A₁ A₁ A₂) → RT H Γ false w A₁ A₁ A₂ := by
                intro w hw A₁ A₂ hr
                refine IH false (fnApp .pi v Z) w A₁ A₁ A₂ ?_ (e.2 w hw) (fun r hr' _ => hr r hr')
                have := depthL_fnApp_le .pi v Z
                have := depth_lt_fn_right (k := .pi) (C := C) (X := Z) hw
                simp only [Bool.toNat_false]; omega
              refine RT.ty_fnPi_iff.2 (.inr ⟨D, E, D', E', hp, fun c hc => ?_, ?_, ?_⟩)
              · refine IH false (args .pi 0 v) c D D D' ?_ (e.1 c hc) (fun r hr _ => hdom r hr)
                have := depthL_args .pi 0 v
                have := Tok.depth_lt_of_mem_dep (t := .fn .pi C Z W) hc
                simp only [Bool.toNat_false]; omega
              · intro N₁ N₁' hNN hZ w hw
                have hr : ∀ r ∈ fnApp .pi v Z,
                    RT H Γ false r (CTm.inst0 N₁ E) (CTm.inst0 N₁ E) (CTm.inst0 N₁' E) ∧
                      RT H Γ false r (CTm.inst0 N₁ E') (CTm.inst0 N₁ E') (CTm.inst0 N₁' E') := by
                  intro r hr
                  obtain ⟨C', Z', W', hm, hZ', hr'⟩ := mem_fnApp.1 hr
                  rcases RT.pi_fam hp hv' hm with hvac | ⟨hf, -⟩
                  · exact ⟨RT.of_vacuous (vacuous_out hvac hr'), RT.of_vacuous (vacuous_out hvac hr')⟩
                  · exact hf N₁ N₁' hNN (hargs hZ hm hZ') r hr'
                exact ⟨hout w hw (fun r h' => (hr r h').1), hout w hw (fun r h' => (hr r h').2)⟩
              · intro N₁ hN₁ hZ w hw
                refine hout w hw (fun r hr => ?_)
                obtain ⟨C', Z', W', hm, hZ', hr'⟩ := mem_fnApp.1 hr
                rcases RT.pi_fam hp hv' hm with hvac | ⟨-, hg⟩
                · exact RT.of_vacuous (vacuous_out hvac hr')
                · exact hg N₁ hN₁ (hargs hZ hm hZ') r hr'
            · obtain ⟨B, y₁, y₂, B', y₁', y₂', hi⟩ := RT.ty_ident_shape hk₀ hn₀ (h s₀ hs₀ hk₀)
              have hcar := RT.ident_carrier hi (fun s hs hk => h s hs hk)
              refine RT.ty_fnIdent_iff.2 (.inr ⟨B, y₁, y₂, B', y₁', y₂', hi, fun c hc => ?_⟩)
              refine IH false (args .ident 0 v) c B B B' ?_ (e.1 c hc) (fun r hr _ => hcar r hr)
              have := depthL_args .ident 0 v
              have := Tok.depth_lt_of_mem_dep (t := .fn .ident C Z W) hc
              simp only [Bool.toNat_false]; omega
            · obtain ⟨D, E, D', E', hp⟩ := RT.ty_sigma_shape hk₀ hn₀ (h s₀ hs₀ hk₀)
              have hv' : ∀ s ∈ v, s.kind = .sigma → RT H Γ false s T x x' :=
                fun s hs hk => h s hs hk
              have hdom := RT.sigma_dom hp hv'
              have hargs : ∀ {N₁ N₁'}, (∀ z ∈ Z, RT H Γ true z D N₁ N₁') →
                  ∀ {C' Z' W'}, Tok.fn .sigma C' Z' W' ∈ v → (∀ z ∈ Z', ent Z z = true) →
                    ∀ z ∈ Z', RT H Γ true z D N₁ N₁' := by
                intro N₁ N₁' hZ C' Z' W' hm hZ' z hz
                refine IH true Z z D N₁ N₁' ?_ (hZ' z hz) (fun q hq _ => hZ q hq)
                have := depthL_lt_fn_left .sigma C Z W
                have := depth_lt_fn_left (k := .sigma) (C := C') (Y := W') hz
                have := Tok.depth_le_of_mem hm
                simp only [Bool.toNat_true]; omega
              have hout : ∀ w, w ∈ W → ∀ {A₁ A₂ : CTm Head n},
                  (∀ r ∈ fnApp .sigma v Z, RT H Γ false r A₁ A₁ A₂) → RT H Γ false w A₁ A₁ A₂ := by
                intro w hw A₁ A₂ hr
                refine IH false (fnApp .sigma v Z) w A₁ A₁ A₂ ?_ (e.2 w hw) (fun r hr' _ => hr r hr')
                have := depthL_fnApp_le .sigma v Z
                have := depth_lt_fn_right (k := .sigma) (C := C) (X := Z) hw
                simp only [Bool.toNat_false]; omega
              refine RT.ty_fnSigma_iff.2 (.inr ⟨D, E, D', E', hp, fun c hc => ?_, ?_, ?_⟩)
              · refine IH false (args .sigma 0 v) c D D D' ?_ (e.1 c hc) (fun r hr _ => hdom r hr)
                have := depthL_args .sigma 0 v
                have := Tok.depth_lt_of_mem_dep (t := .fn .sigma C Z W) hc
                simp only [Bool.toNat_false]; omega
              · intro N₁ N₁' hNN hZ w hw
                have hr : ∀ r ∈ fnApp .sigma v Z,
                    RT H Γ false r (CTm.inst0 N₁ E) (CTm.inst0 N₁ E) (CTm.inst0 N₁' E) ∧
                      RT H Γ false r (CTm.inst0 N₁ E') (CTm.inst0 N₁ E') (CTm.inst0 N₁' E') := by
                  intro r hr
                  obtain ⟨C', Z', W', hm, hZ', hr'⟩ := mem_fnApp.1 hr
                  rcases RT.sigma_fam hp hv' hm with hvac | ⟨hf, -⟩
                  · exact ⟨RT.of_vacuous (vacuous_out hvac hr'), RT.of_vacuous (vacuous_out hvac hr')⟩
                  · exact hf N₁ N₁' hNN (hargs hZ hm hZ') r hr'
                exact ⟨hout w hw (fun r h' => (hr r h').1), hout w hw (fun r h' => (hr r h').2)⟩
              · intro N₁ hN₁ hZ w hw
                refine hout w hw (fun r hr => ?_)
                obtain ⟨C', Z', W', hm, hZ', hr'⟩ := mem_fnApp.1 hr
                rcases RT.sigma_fam hp hv' hm with hvac | ⟨-, hg⟩
                · exact RT.of_vacuous (vacuous_out hvac hr')
                · exact hg N₁ hN₁ (hargs hZ hm hZ') r hr'
            · obtain ⟨dn, rfl⟩ := hk
              have hpar := RT.data_params (fun s hs hk => h s hs hk)
              refine RT.ty_fnData_iff.2 (.inr ⟨RT.ty_data_shape hk₀ hn₀ (h s₀ hs₀ hk₀),
                fun c hc B hB => ?_⟩)
              refine IH false (args (.data dn) 0 v) c B B B ?_ (e.1 c hc)
                (fun r hr _ => hpar 0 r hr B hB)
              have := depthL_args (.data dn) 0 v
              have := Tok.depth_lt_of_mem_dep (t := .fn (.data dn) C Z W) hc
              simp only [Bool.toNat_false]; omega
            · exact RT.ty_fn_other hk
        | true =>
            simp only [Bool.toNat_true] at hN
            have e' := e
            rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at e
            cases htk : typeKind k with
            | true =>
                have htk' : typeKind (Tok.fn k C Z W).kind = true := htk
                have htk₀ : typeKind s₀.kind = true := by rw [hk₀]; exact htk'
                have hstep : ∀ {s}, s ∈ v → s.kind = (Tok.fn k C Z W).kind →
                    ∀ {h₀ : Head}, CRedTy H Γ T (.head h₀) → RT H Γ false s x x x' := by
                  intro s hs hk h₀ hred
                  have hts : typeKind s.kind = true := by rw [hk]; exact htk'
                  rcases (RT.tm_type_iff hts).1 (h s hs hk) with hvac | ⟨_, _, _, hr⟩ | ⟨hp, _⟩
                  · exact RT.of_vacuous hvac
                  · exact hr
                  · exact (CRedTy.head_ne_prop hred hp).elim
                have hstep' : ∀ {s}, s ∈ v → s.kind = (Tok.fn k C Z W).kind →
                    CRedTy H Γ T (.const K.prop) →
                      RT H Γ false s (.app (.const K.holds) x) (.app (.const K.holds) x)
                        (.app (.const K.holds) x') := by
                  intro s hs hk hprop
                  have hts : typeKind s.kind = true := by rw [hk]; exact htk'
                  rcases (RT.tm_type_iff hts).1 (h s hs hk) with hvac | ⟨_, _, hred, _⟩ | ⟨_, hr⟩
                  · exact RT.of_vacuous hvac
                  · exact (CRedTy.head_ne_prop hred hprop).elim
                  · exact hr
                rcases (RT.tm_type_iff htk₀).1 (h s₀ hs₀ hk₀) with hvac | ⟨h₀, hu₀, hred, _⟩ |
                  ⟨hp, _⟩
                · rw [hvac] at hn₀; cases hn₀
                · refine (RT.tm_type_iff htk').2 (.inr (.inl ⟨h₀, hu₀, hred, ?_⟩))
                  exact IH false v _ x x x' (by simp only [Bool.toNat_false]; omega) e'
                    (fun s hs hk => hstep hs hk hred)
                · refine (RT.tm_type_iff htk').2 (.inr (.inr ⟨hp, ?_⟩))
                  exact IH false v _ _ _ _ (by simp only [Bool.toNat_false]; omega) e'
                    (fun s hs hk => hstep' hs hk hp)
            | false =>
                rcases kind_cases_tmPair k with rfl | rfl | rfl | rfl | hk | hk
                · -- function entries
                  refine RT.tm_lam_iff.2 (.inr fun D E hT => ?_)
                  have hent : ∀ {C' X' Y'}, Tok.fn .lam C' X' Y' ∈ v →
                      ent [] (.fn .lam C' X' Y') = true ∨
                        ((∀ N N', CEqual P Γ N N' D → (∀ z ∈ X', RT H Γ true z D N N') →
                          ∀ y ∈ Y', RT H Γ true y (CTm.inst0 N E) (.app x N) (.app x N') ∧
                            RT H Γ true y (CTm.inst0 N E) (.app x' N) (.app x' N')) ∧
                        (∀ N, CTyped P Γ N D → (∀ z ∈ X', RT H Γ true z D N N) →
                          ∀ y ∈ Y', RT H Γ true y (CTm.inst0 N E) (.app x N) (.app x' N))) := by
                    intro C' X' Y' hm
                    rcases RT.tm_lam_iff.1 (h _ hm rfl) with hvac | hcl
                    · exact .inl hvac
                    · exact .inr (hcl D E hT)
                  have hargs : ∀ {N₁ N₁'}, (∀ z ∈ Z, RT H Γ true z D N₁ N₁') →
                      ∀ {C' X' Y'}, Tok.fn .lam C' X' Y' ∈ v → (∀ z ∈ X', ent Z z = true) →
                        ∀ z ∈ X', RT H Γ true z D N₁ N₁' := by
                    intro N₁ N₁' hZ C' X' Y' hm hX' z hz
                    refine IH true Z z D N₁ N₁' ?_ (hX' z hz) (fun q hq _ => hZ q hq)
                    have := depthL_lt_fn_left .lam C Z W
                    have := depth_lt_fn_left (k := .lam) (C := C') (Y := Y') hz
                    have := Tok.depth_le_of_mem hm
                    simp only [Bool.toNat_true]; omega
                  have hout : ∀ w, w ∈ W → ∀ {S M₁ M₂ : CTm Head n},
                      (∀ r ∈ fnApp .lam v Z, RT H Γ true r S M₁ M₂) → RT H Γ true w S M₁ M₂ := by
                    intro w hw S M₁ M₂ hr
                    refine IH true (fnApp .lam v Z) w S M₁ M₂ ?_ (e.2 w hw) (fun r hr' _ => hr r hr')
                    have := depthL_fnApp_le .lam v Z
                    have := depth_lt_fn_right (k := .lam) (C := C) (X := Z) hw
                    simp only [Bool.toNat_true]; omega
                  refine ⟨fun N₁ N₁' hNN hZ w hw => ?_, fun N₁ hN₁ hZ w hw => ?_⟩
                  · have hr : ∀ r ∈ fnApp .lam v Z,
                        RT H Γ true r (CTm.inst0 N₁ E) (.app x N₁) (.app x N₁') ∧
                          RT H Γ true r (CTm.inst0 N₁ E) (.app x' N₁) (.app x' N₁') := by
                      intro r hr
                      obtain ⟨C', X', Y', hm, hX', hr'⟩ := mem_fnApp.1 hr
                      rcases hent hm with hvac | ⟨hf, -⟩
                      · exact ⟨RT.of_vacuous (vacuous_out hvac hr'),
                          RT.of_vacuous (vacuous_out hvac hr')⟩
                      · exact hf N₁ N₁' hNN (hargs hZ hm hX') r hr'
                    exact ⟨hout w hw (fun r h' => (hr r h').1), hout w hw (fun r h' => (hr r h').2)⟩
                  · refine hout w hw (fun r hr => ?_)
                    obtain ⟨C', X', Y', hm, hX', hr'⟩ := mem_fnApp.1 hr
                    rcases hent hm with hvac | ⟨-, hg⟩
                    · exact RT.of_vacuous (vacuous_out hvac hr')
                    · exact hg N₁ hN₁ (hargs hZ hm hX') r hr'
                · obtain ⟨B, y₁, y₂, r, r', hr⟩ := RT.tm_refl_shape hk₀ hn₀ (h s₀ hs₀ hk₀)
                  have hpts := RT.refl_points hr (fun s hs hk => h s hs hk)
                  refine RT.tm_fnRefl_iff.2 (.inr ⟨B, y₁, y₂, r, r', hr, fun c hc => ?_⟩)
                  have := depthL_args .refl 0 v
                  have := Tok.depth_lt_of_mem_dep (t := .fn .refl C Z W) hc
                  refine ⟨IH true (args .refl 0 v) c B r y₁ ?_ (e.1 c hc) (fun q hq _ => (hpts q hq).1),
                    IH true (args .refl 0 v) c B r y₂ ?_ (e.1 c hc) (fun q hq _ => (hpts q hq).2.1),
                    IH true (args .refl 0 v) c B r r' ?_ (e.1 c hc) (fun q hq _ => (hpts q hq).2.2)⟩ <;>
                  · simp only [Bool.toNat_true]; omega
                · obtain ⟨m, m', hs⟩ := RT.tm_succ_shape hk₀ hn₀ (h s₀ hs₀ hk₀)
                  have hpred := RT.succ_pred hs (fun s hs hk => h s hs hk)
                  refine RT.tm_fnSucc_iff.2 (.inr ⟨m, m', hs, fun c hc => ?_⟩)
                  have := depthL_args .succ 0 v
                  have := Tok.depth_lt_of_mem_dep (t := .fn .succ C Z W) hc
                  exact IH true (args .succ 0 v) c _ m m' (by simp only [Bool.toNat_true]; omega)
                    (e.1 c hc) (fun q hq _ => hpred q hq)
                · refine RT.tm_fnPair_iff.2 (.inr fun D E hT =>
                    ⟨RT.tm_pair_core hk₀ hn₀ (h s₀ hs₀ hk₀) D E hT, fun c hc => ?_⟩)
                  have hfirst := RT.pair_first hT (fun s hs hk => h s hs hk)
                  have := depthL_args .pair 0 v
                  have := Tok.depth_lt_of_mem_dep (t := .fn .pair C Z W) hc
                  exact IH true (args .pair 0 v) c _ _ _ (by simp only [Bool.toNat_true]; omega)
                    (e.1 c hc) (fun r hr _ => hfirst r hr)
                · obtain ⟨dn, cn, fs, rfl⟩ := hk
                  obtain ⟨ms, ms', hs⟩ := RT.tm_ctor_shape hk₀ hn₀ (h s₀ hs₀ hk₀)
                  have hfld := RT.ctor_fields hs (fun s hs hk => h s hs hk)
                  refine RT.tm_fnCtor_iff.2 (.inr ⟨ms, ms', hs, fun c hc A m m' hA => ?_⟩)
                  have := depthL_args (.ctor dn cn fs) 0 v
                  have := Tok.depth_lt_of_mem_dep (t := .fn (.ctor dn cn fs) C Z W) hc
                  exact IH true (args (.ctor dn cn fs) 0 v) c A m m'
                    (by simp only [Bool.toNat_true]; omega) (e.1 c hc)
                    (fun r hr _ => hfld 0 r hr A m m' hA)
                · exact RT.tm_other htk (fun _ _ _ e => by cases e; exact hk.1 rfl) hk.2.1
                    (fun e => nomatch e) hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2

/-- **Closure under entailment**: a token entailed by a list relates what the
tokens of its kind in the list all relate. -/
theorem RT.closed {b : Bool} {v : List Tok} {t : Tok} {T x x' : CTm Head n}
    (e : ent v t = true) (h : ∀ s ∈ v, s.kind = t.kind → RT H Γ b s T x x') : RT H Γ b t T x x' :=
  RT.closed_aux _ b v t T x x' (Nat.lt_succ_self _) e h

/-- Closure under entailment, from all the tokens of a list. -/
theorem RT.closed' {b : Bool} {v : List Tok} {t : Tok} {T x x' : CTm Head n}
    (e : ent v t = true) (h : ∀ s ∈ v, RT H Γ b s T x x') : RT H Γ b t T x x' :=
  RT.closed e fun s hs _ => h s hs

end Closure

/-! ## Head expansion -/

section Expansion

variable {H} {L : Type} [LevelOrder L] (levels : LevelModel R L) {n : Nat} {Γ : CCtx Head n}
include levels

/-- **Head expansion of types**: types related as far as a token observes stay
related when either is replaced by a type that reduces to it. -/
theorem RT.expand_ty {t : Tok} {T T' x x' y y' : CTm Head n} (rx : CRedTy H Γ x y)
    (rx' : CRedTy H Γ x' y') (h : RT H Γ false t T y y') : RT H Γ false t T' x x' := by
  have pi : ∀ {D D' : CTm Head n} {E E' : CTm Head (n + 1)}, PiRed H Γ y y' D E D' E' →
      PiRed H Γ x x' D E D' E' := fun ⟨r, r', e, e'⟩ =>
    ⟨rx.trans levels r, rx'.trans levels r', e, e'⟩
  have sigma : ∀ {D D' : CTm Head n} {E E' : CTm Head (n + 1)}, SigmaRed H Γ y y' D E D' E' →
      SigmaRed H Γ x x' D E D' E' := fun ⟨r, r', e, e'⟩ =>
    ⟨rx.trans levels r, rx'.trans levels r', e, e'⟩
  have idr : ∀ {B z₁ z₂ B' z₁' z₂' : CTm Head n}, IdRed H Γ y y' B z₁ z₂ B' z₁' z₂' →
      IdRed H Γ x x' B z₁ z₂ B' z₁' z₂' := fun ⟨r, r', e₁, e₂, e₃⟩ =>
    ⟨rx.trans levels r, rx'.trans levels r', e₁, e₂, e₃⟩
  have data : ∀ {d : DeclName}, DataRed H Γ d y y' → DataRed H Γ d x x' := fun ⟨hd, r, r'⟩ =>
    ⟨hd, rx.trans levels r, rx'.trans levels r'⟩
  cases hv : ent [] t with
  | true => exact RT.of_vacuous hv
  | false =>
  cases t with
  | tag k =>
      cases k
      case univ =>
        obtain ⟨h₁, h₂, r₁, r₂, u₁, u₂, same⟩ := RT.ty_univ_iff.1 h
        exact RT.ty_univ_iff.2 ⟨h₁, h₂, rx.trans levels r₁, rx'.trans levels r₂, u₁, u₂, same⟩
      case codes =>
        obtain ⟨r₁, r₂⟩ := RT.ty_codes_iff.1 h
        exact RT.ty_codes_iff.2 ⟨rx.trans levels r₁, rx'.trans levels r₂⟩
      case nat =>
        obtain ⟨r₁, r₂⟩ := RT.ty_nat_iff.1 h
        exact RT.ty_nat_iff.2 ⟨rx.trans levels r₁, rx'.trans levels r₂⟩
      case pi =>
        obtain ⟨D, E, D', E', hp⟩ := RT.ty_pi_iff.1 h
        exact RT.ty_pi_iff.2 ⟨D, E, D', E', pi hp⟩
      case ident =>
        obtain ⟨B, z₁, z₂, B', z₁', z₂', hi⟩ := RT.ty_ident_iff.1 h
        exact RT.ty_ident_iff.2 ⟨B, z₁, z₂, B', z₁', z₂', idr hi⟩
      case ground =>
        obtain ⟨g, hg, r₁, r₂⟩ := RT.ty_ground_iff.1 h
        exact RT.ty_ground_iff.2 ⟨g, hg, rx.trans levels r₁, rx'.trans levels r₂⟩
      case sigma =>
        obtain ⟨D, E, D', E', hp⟩ := RT.ty_sigma_iff.1 h
        exact RT.ty_sigma_iff.2 ⟨D, E, D', E', sigma hp⟩
      case data d => exact RT.ty_data_iff.2 (data (RT.ty_data_iff.1 h))
      all_goals exact RT.ty_tag_other (by simp)
  | arg k i C d =>
      rcases kind_cases_tySigma k with rfl | rfl | rfl | ⟨dn, rfl⟩ | hk
      · rcases RT.ty_argPi_iff.1 h with hvac | ⟨D, E, D', E', hp, rest⟩
        · exact RT.of_vacuous hvac
        · exact RT.ty_argPi_iff.2 (.inr ⟨D, E, D', E', pi hp, rest⟩)
      · rcases RT.ty_argIdent_iff.1 h with hvac | ⟨B, z₁, z₂, B', z₁', z₂', hi, rest⟩
        · exact RT.of_vacuous hvac
        · exact RT.ty_argIdent_iff.2 (.inr ⟨B, z₁, z₂, B', z₁', z₂', idr hi, rest⟩)
      · rcases RT.ty_argSigma_iff.1 h with hvac | ⟨D, E, D', E', hp, rest⟩
        · exact RT.of_vacuous hvac
        · exact RT.ty_argSigma_iff.2 (.inr ⟨D, E, D', E', sigma hp, rest⟩)
      · rcases RT.ty_param_iff.1 h with hvac | ⟨hd, rest⟩
        · exact RT.of_vacuous hvac
        · exact RT.ty_param_iff.2 (.inr ⟨data hd, rest⟩)
      · exact RT.ty_arg_other hk
  | fn k C Z W =>
      rcases kind_cases_tySigma k with rfl | rfl | rfl | ⟨dn, rfl⟩ | hk
      · rcases RT.ty_fnPi_iff.1 h with hvac | ⟨D, E, D', E', hp, rest⟩
        · exact RT.of_vacuous hvac
        · exact RT.ty_fnPi_iff.2 (.inr ⟨D, E, D', E', pi hp, rest⟩)
      · rcases RT.ty_fnIdent_iff.1 h with hvac | ⟨B, z₁, z₂, B', z₁', z₂', hi, rest⟩
        · exact RT.of_vacuous hvac
        · exact RT.ty_fnIdent_iff.2 (.inr ⟨B, z₁, z₂, B', z₁', z₂', idr hi, rest⟩)
      · rcases RT.ty_fnSigma_iff.1 h with hvac | ⟨D, E, D', E', hp, rest⟩
        · exact RT.of_vacuous hvac
        · exact RT.ty_fnSigma_iff.2 (.inr ⟨D, E, D', E', sigma hp, rest⟩)
      · rcases RT.ty_fnData_iff.1 h with hvac | ⟨hd, rest⟩
        · exact RT.of_vacuous hvac
        · exact RT.ty_fnData_iff.2 (.inr ⟨data hd, rest⟩)
      · exact RT.ty_fn_other hk

/-- **Head reduction of types**: types related as far as a token observes stay
related when either is replaced by a type it reduces to. -/
theorem RT.reduce_ty {t : Tok} {T T' x x' y y' : CTm Head n} (rx : CRedTy H Γ x y)
    (rx' : CRedTy H Γ x' y') (h : RT H Γ false t T x x') : RT H Γ false t T' y y' := by
  have pi : ∀ {D D' : CTm Head n} {E E' : CTm Head (n + 1)}, PiRed H Γ x x' D E D' E' →
      PiRed H Γ y y' D E D' E' := fun ⟨r, r', e, e'⟩ =>
    ⟨CRedTy.reduce levels rx r (H.normal_pi _ _), CRedTy.reduce levels rx' r' (H.normal_pi _ _),
      e, e'⟩
  have sigma : ∀ {D D' : CTm Head n} {E E' : CTm Head (n + 1)}, SigmaRed H Γ x x' D E D' E' →
      SigmaRed H Γ y y' D E D' E' := fun ⟨r, r', e, e'⟩ =>
    ⟨CRedTy.reduce levels rx r (H.normal_sigma _ _),
      CRedTy.reduce levels rx' r' (H.normal_sigma _ _), e, e'⟩
  have idr : ∀ {B z₁ z₂ B' z₁' z₂' : CTm Head n}, IdRed H Γ x x' B z₁ z₂ B' z₁' z₂' →
      IdRed H Γ y y' B z₁ z₂ B' z₁' z₂' := fun ⟨r, r', e₁, e₂, e₃⟩ =>
    ⟨CRedTy.reduce levels rx r (H.normal_id _ _ _), CRedTy.reduce levels rx' r' (H.normal_id _ _ _),
      e₁, e₂, e₃⟩
  have data : ∀ {d : DeclName}, DataRed H Γ d x x' → DataRed H Γ d y y' := fun ⟨hd, r, r'⟩ =>
    ⟨hd, CRedTy.reduce levels rx r (H.normal_data hd), CRedTy.reduce levels rx' r' (H.normal_data hd)⟩
  cases hv : ent [] t with
  | true => exact RT.of_vacuous hv
  | false =>
  cases t with
  | tag k =>
      cases k
      case univ =>
        obtain ⟨h₁, h₂, r₁, r₂, u₁, u₂, same⟩ := RT.ty_univ_iff.1 h
        exact RT.ty_univ_iff.2 ⟨h₁, h₂, CRedTy.reduce levels rx r₁ (H.normal_head _),
          CRedTy.reduce levels rx' r₂ (H.normal_head _), u₁, u₂, same⟩
      case codes =>
        obtain ⟨r₁, r₂⟩ := RT.ty_codes_iff.1 h
        exact RT.ty_codes_iff.2 ⟨CRedTy.reduce levels rx r₁ H.normal_prop,
          CRedTy.reduce levels rx' r₂ H.normal_prop⟩
      case nat =>
        obtain ⟨r₁, r₂⟩ := RT.ty_nat_iff.1 h
        exact RT.ty_nat_iff.2 ⟨CRedTy.reduce levels rx r₁ H.normal_num,
          CRedTy.reduce levels rx' r₂ H.normal_num⟩
      case pi =>
        obtain ⟨D, E, D', E', hp⟩ := RT.ty_pi_iff.1 h
        exact RT.ty_pi_iff.2 ⟨D, E, D', E', pi hp⟩
      case ident =>
        obtain ⟨B, z₁, z₂, B', z₁', z₂', hi⟩ := RT.ty_ident_iff.1 h
        exact RT.ty_ident_iff.2 ⟨B, z₁, z₂, B', z₁', z₂', idr hi⟩
      case ground =>
        obtain ⟨g, hg, r₁, r₂⟩ := RT.ty_ground_iff.1 h
        exact RT.ty_ground_iff.2 ⟨g, hg, CRedTy.reduce levels rx r₁ (H.normal_ground hg),
          CRedTy.reduce levels rx' r₂ (H.normal_ground hg)⟩
      case sigma =>
        obtain ⟨D, E, D', E', hp⟩ := RT.ty_sigma_iff.1 h
        exact RT.ty_sigma_iff.2 ⟨D, E, D', E', sigma hp⟩
      case data d => exact RT.ty_data_iff.2 (data (RT.ty_data_iff.1 h))
      all_goals exact RT.ty_tag_other (by simp)
  | arg k i C d =>
      rcases kind_cases_tySigma k with rfl | rfl | rfl | ⟨dn, rfl⟩ | hk
      · rcases RT.ty_argPi_iff.1 h with hvac | ⟨D, E, D', E', hp, rest⟩
        · exact RT.of_vacuous hvac
        · exact RT.ty_argPi_iff.2 (.inr ⟨D, E, D', E', pi hp, rest⟩)
      · rcases RT.ty_argIdent_iff.1 h with hvac | ⟨B, z₁, z₂, B', z₁', z₂', hi, rest⟩
        · exact RT.of_vacuous hvac
        · exact RT.ty_argIdent_iff.2 (.inr ⟨B, z₁, z₂, B', z₁', z₂', idr hi, rest⟩)
      · rcases RT.ty_argSigma_iff.1 h with hvac | ⟨D, E, D', E', hp, rest⟩
        · exact RT.of_vacuous hvac
        · exact RT.ty_argSigma_iff.2 (.inr ⟨D, E, D', E', sigma hp, rest⟩)
      · rcases RT.ty_param_iff.1 h with hvac | ⟨hd, rest⟩
        · exact RT.of_vacuous hvac
        · exact RT.ty_param_iff.2 (.inr ⟨data hd, rest⟩)
      · exact RT.ty_arg_other hk
  | fn k C Z W =>
      rcases kind_cases_tySigma k with rfl | rfl | rfl | ⟨dn, rfl⟩ | hk
      · rcases RT.ty_fnPi_iff.1 h with hvac | ⟨D, E, D', E', hp, rest⟩
        · exact RT.of_vacuous hvac
        · exact RT.ty_fnPi_iff.2 (.inr ⟨D, E, D', E', pi hp, rest⟩)
      · rcases RT.ty_fnIdent_iff.1 h with hvac | ⟨B, z₁, z₂, B', z₁', z₂', hi, rest⟩
        · exact RT.of_vacuous hvac
        · exact RT.ty_fnIdent_iff.2 (.inr ⟨B, z₁, z₂, B', z₁', z₂', idr hi, rest⟩)
      · rcases RT.ty_fnSigma_iff.1 h with hvac | ⟨D, E, D', E', hp, rest⟩
        · exact RT.of_vacuous hvac
        · exact RT.ty_fnSigma_iff.2 (.inr ⟨D, E, D', E', sigma hp, rest⟩)
      · rcases RT.ty_fnData_iff.1 h with hvac | ⟨hd, rest⟩
        · exact RT.of_vacuous hvac
        · exact RT.ty_fnData_iff.2 (.inr ⟨data hd, rest⟩)
      · exact RT.ty_fn_other hk

omit levels in
/-- The typed reduction of the decoded code follows the typed reduction of the code. -/
theorem CRedTm.holds {c c' T : CTm Head n} (r : CRedTm H Γ c c' T)
    (hT : CRedTy H Γ T (.const K.prop)) :
    CRedTy H Γ (.app (.const K.holds) c) (.app (.const K.holds) c') := by
  obtain ⟨u, hu, th⟩ := K.holds_typed Γ
  exact ⟨H.red_holds r.1, u, hu, CDerivable.appCong (.refl th) (r.2.convType hT.2)⟩

omit levels in
/-- A typed reduction at a universe is a typed reduction of types. -/
theorem CRedTm.toTy {x y T : CTm Head n} {h : Head} (r : CRedTm H Γ x y T) (hu : R.isUniverse h)
    (hT : CRedTy H Γ T (.head h)) : CRedTy H Γ x y :=
  ⟨r.1, h, hu, r.2.convType hT.2⟩

omit levels in
/-- The applications of two terms to one argument reduce as the functions do. -/
theorem CRedTm.app {f g N T D : CTm Head n} {E : CTm Head (n + 1)} (r : CRedTm H Γ f g T)
    (hT : CRedTy H Γ T (.pi D E)) (tN : CTyped P Γ N D) :
    CRedTm H Γ (.app f N) (.app g N) (CTm.inst0 N E) :=
  ⟨H.red_app r.1 N, CDerivable.appCong (r.2.convType hT.2) (.refl tN)⟩

omit levels in
/-- A reduction at the instance of a family at an argument equal to another. -/
theorem CRedTm.retype {a b N N' D : CTm Head n} {E : CTm Head (n + 1)}
    (r : CRedTm H Γ a b (CTm.inst0 N' E)) (hE : CIsType P (.snoc Γ D) E) (tN' : CTyped P Γ N' D)
    (e : CEqual P Γ N' N D) : CRedTm H Γ a b (CTm.inst0 N E) :=
  r.convType (hE.instantiateEq tN' e)

omit levels in
/-- The first projections of two terms reduce as the terms do. -/
theorem CRedTm.fst {p q T D : CTm Head n} {E : CTm Head (n + 1)} (r : CRedTm H Γ p q T)
    (hT : CRedTy H Γ T (.sigma D E)) : CRedTm H Γ (.fst p) (.fst q) D :=
  ⟨H.red_fst r.1, CDerivable.fstCong (r.2.convType hT.2)⟩

omit levels in
/-- The second projections of two terms reduce as the terms do, at the family's value
at the first projection of the first. -/
theorem CRedTm.snd {p q T D : CTm Head n} {E : CTm Head (n + 1)} (r : CRedTm H Γ p q T)
    (hT : CRedTy H Γ T (.sigma D E)) :
    CRedTm H Γ (.snd p) (.snd q) (CTm.inst0 (.fst p) E) :=
  ⟨H.red_snd r.1, CDerivable.sndCong (r.2.convType hT.2)⟩

/-- **Head expansion**: terms related at a type as far as a token observes stay
related when either is replaced by a term that reduces to it at that type. -/
theorem RT.expand_aux (formed : CCtxFormed P Γ) : ∀ (N : Nat) (t : Tok), t.depth < N →
    ∀ (T x x' y y' : CTm Head n), CRedTm H Γ x y T → CRedTm H Γ x' y' T →
      RT H Γ true t T y y' → RT H Γ true t T x x'
  | 0, _, hN => absurd hN (Nat.not_lt_zero _)
  | N + 1, t, hN => by
    intro T x x' y y' rx rx' h
    have IH := fun t ht {T x x' y y' : CTm Head n} => RT.expand_aux formed N t ht T x x' y y'
    cases hv : ent [] t with
    | true => exact RT.of_vacuous hv
    | false =>
    cases htk : typeKind t.kind with
    | true =>
        rcases (RT.tm_type_iff htk).1 h with hvac | ⟨h₀, hu, hT, hr⟩ | ⟨hT, hr⟩
        · exact RT.of_vacuous hvac
        · exact (RT.tm_type_iff htk).2 (.inr (.inl ⟨h₀, hu, hT,
            RT.expand_ty levels (rx.toTy hu hT) (rx'.toTy hu hT) hr⟩))
        · exact (RT.tm_type_iff htk).2 (.inr (.inr ⟨hT,
            RT.expand_ty levels (rx.holds hT) (rx'.holds hT) hr⟩))
    | false =>
    have refl : ∀ {B z₁ z₂ r r' : CTm Head n}, ReflRed H Γ T y y' B z₁ z₂ r r' →
        ReflRed H Γ T x x' B z₁ z₂ r r' := fun ⟨hT, r₁, r₂, e₁, e₂, e₃⟩ =>
      ⟨hT, rx.trans r₁, rx'.trans r₂, e₁, e₂, e₃⟩
    have succ : ∀ {m m' : CTm Head n}, SuccRed H Γ T y y' m m' → SuccRed H Γ T x x' m m' :=
      fun ⟨hT, r₁, r₂, e⟩ => ⟨hT, rx.trans r₁, rx'.trans r₂, e⟩
    have ctor : ∀ {d c : DeclName} {fs : List FieldShape} {ms ms' : List (CTm Head n)},
        CtorRed H Γ d c fs T y y' ms ms' → CtorRed H Γ d c fs T x x' ms ms' :=
      fun ⟨hc, hT, r₁, r₂, fe⟩ => ⟨hc, hT, rx.trans r₁, rx'.trans r₂, fe⟩
    -- the first projections of the pairs
    have core : ∀ {D : CTm Head n} {E : CTm Head (n + 1)}, CRedTy H Γ T (.sigma D E) →
        CEqual P Γ (.fst y) (.fst y') D → CEqual P Γ (.fst x) (.fst x') D := fun hT e =>
      .trans (rx.fst hT).2 (.trans e (.symm (rx'.fst hT).2))
    cases t with
    | tag k =>
        cases k
        case refl =>
          obtain ⟨B, z₁, z₂, r, r', hr⟩ := RT.tm_reflTag_iff.1 h
          exact RT.tm_reflTag_iff.2 ⟨B, z₁, z₂, r, r', refl hr⟩
        case zero =>
          obtain ⟨hT, r₁, r₂⟩ := RT.tm_zero_iff.1 h
          exact RT.tm_zero_iff.2 ⟨hT, rx.trans r₁, rx'.trans r₂⟩
        case succ =>
          obtain ⟨m, m', hs⟩ := RT.tm_succTag_iff.1 h
          exact RT.tm_succTag_iff.2 ⟨m, m', succ hs⟩
        case pair =>
          exact RT.tm_pairTag_iff.2 fun D E hT => core hT (RT.tm_pairTag_iff.1 h D E hT)
        case ctor d c fs =>
          obtain ⟨ms, ms', hs⟩ := RT.tm_ctorTag_iff.1 h
          exact RT.tm_ctorTag_iff.2 ⟨ms, ms', ctor hs⟩
        all_goals
          exact RT.tm_other htk (fun _ _ _ e => nomatch e)
            (by intro e; cases e) (by intro e; cases e) (by intro e; cases e) (by intro e; cases e)
            (fun _ _ _ e => nomatch e)
    | arg k i C d =>
        rcases kind_cases_tmPair k with rfl | rfl | rfl | rfl | ⟨dn, cn, fs, rfl⟩ | hk
        · exact RT.tm_other htk (fun _ _ _ e => nomatch e) (by intro e; cases e)
            (fun e => nomatch e) (by intro e; cases e) (by intro e; cases e)
            (fun _ _ _ e => nomatch e)
        · rcases RT.tm_argRefl_iff.1 h with hvac | ⟨B, z₁, z₂, r, r', hr, rest⟩
          · exact RT.of_vacuous hvac
          · exact RT.tm_argRefl_iff.2 (.inr ⟨B, z₁, z₂, r, r', refl hr, rest⟩)
        · rcases RT.tm_argSucc_iff.1 h with hvac | ⟨m, m', hs, rest⟩
          · exact RT.of_vacuous hvac
          · exact RT.tm_argSucc_iff.2 (.inr ⟨m, m', succ hs, rest⟩)
        · rcases RT.tm_argPair_iff.1 h with hvac | hcl
          · exact RT.of_vacuous hvac
          refine RT.tm_argPair_iff.2 (.inr fun D E hT => ?_)
          obtain ⟨e₀, hC, h0, h1⟩ := hcl D E hT
          have hE : CIsType P (.snoc Γ D) E :=
            ((CTypeEq.isType levels hT.2 formed).2.sigma_parts).2
          have ex : CEqual P Γ (.fst x) (.fst x') D := core hT e₀
          refine ⟨ex, fun c hc => ?_, fun hi => ?_, fun hi N₁ Q hQ hNQ => ?_⟩
          · have hc' : c.depth < N := by
              have := Tok.depth_lt_of_mem_dep (t := .arg .pair i C d) hc; omega
            exact IH c hc' (rx.fst hT) (rx'.fst hT) (hC c hc)
          · have hd' : d.depth < N := by have := depth_lt_arg .pair i C d; omega
            exact IH d hd' (rx.fst hT) (rx'.fst hT) (h0 hi)
          · have hd' : d.depth < N := by have := depth_lt_arg .pair i C d; omega
            obtain ⟨Q', hQ', hNQ'⟩ := CRedTm.join_of_red (rx.fst hT) hQ hNQ
            have tx : CTyped P Γ (.fst x) D := (CEqual.typed levels ex formed).1
            have exN : CEqual P Γ (.fst x) N₁ D := .trans hQ.2 (.symm hNQ.2)
            exact IH d hd' ((rx.snd hT).retype hE tx exN)
              ((rx'.snd hT).retype hE (CEqual.typed levels ex formed).2 (.trans (.symm ex) exN))
              (h1 hi N₁ Q' hQ' hNQ')
        · rcases RT.tm_field_iff.1 h with hvac | ⟨ms, ms', hs, rest⟩
          · exact RT.of_vacuous hvac
          · exact RT.tm_field_iff.2 (.inr ⟨ms, ms', ctor hs, rest⟩)
        · exact RT.tm_other htk (fun _ _ _ e => nomatch e) hk.2.1
            (fun e => nomatch e) hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2
    | fn k C X Y =>
        rcases kind_cases_tmPair k with rfl | rfl | rfl | rfl | ⟨dn, cn, fs, rfl⟩ | hk
        · rcases RT.tm_lam_iff.1 h with hvac | hcl
          · exact RT.of_vacuous hvac
          refine RT.tm_lam_iff.2 (.inr fun D E hT => ?_)
          obtain ⟨hi, hii⟩ := hcl D E hT
          have hE : CIsType P (.snoc Γ D) E :=
            ((CTypeEq.isType levels hT.2 formed).2.pi_parts).2
          refine ⟨fun N₁ N₁' hNN hX y₀ hy₀ => ?_, fun N₁ tN₁ hX y₀ hy₀ => ?_⟩
          · obtain ⟨tN₁, tN₁'⟩ := CEqual.typed levels hNN formed
            have hy₀' : y₀.depth < N := by
              have := depth_lt_fn_right (k := .lam) (C := C) (X := X) hy₀; omega
            obtain ⟨h₁, h₂⟩ := hi N₁ N₁' hNN hX y₀ hy₀
            exact ⟨IH y₀ hy₀' (rx.app hT tN₁) ((rx.app hT tN₁').retype hE tN₁' (.symm hNN)) h₁,
              IH y₀ hy₀' (rx'.app hT tN₁) ((rx'.app hT tN₁').retype hE tN₁' (.symm hNN)) h₂⟩
          · have hy₀' : y₀.depth < N := by
              have := depth_lt_fn_right (k := .lam) (C := C) (X := X) hy₀; omega
            exact IH y₀ hy₀' (rx.app hT tN₁) (rx'.app hT tN₁) (hii N₁ tN₁ hX y₀ hy₀)
        · rcases RT.tm_fnRefl_iff.1 h with hvac | ⟨B, z₁, z₂, r, r', hr, rest⟩
          · exact RT.of_vacuous hvac
          · exact RT.tm_fnRefl_iff.2 (.inr ⟨B, z₁, z₂, r, r', refl hr, rest⟩)
        · rcases RT.tm_fnSucc_iff.1 h with hvac | ⟨m, m', hs, rest⟩
          · exact RT.of_vacuous hvac
          · exact RT.tm_fnSucc_iff.2 (.inr ⟨m, m', succ hs, rest⟩)
        · rcases RT.tm_fnPair_iff.1 h with hvac | hcl
          · exact RT.of_vacuous hvac
          refine RT.tm_fnPair_iff.2 (.inr fun D E hT => ?_)
          obtain ⟨e₀, hC⟩ := hcl D E hT
          refine ⟨core hT e₀, fun c hc => ?_⟩
          have hc' : c.depth < N := by
            have := Tok.depth_lt_of_mem_dep (t := .fn .pair C X Y) hc; omega
          exact IH c hc' (rx.fst hT) (rx'.fst hT) (hC c hc)
        · rcases RT.tm_fnCtor_iff.1 h with hvac | ⟨ms, ms', hs, rest⟩
          · exact RT.of_vacuous hvac
          · exact RT.tm_fnCtor_iff.2 (.inr ⟨ms, ms', ctor hs, rest⟩)
        · exact RT.tm_other htk (fun _ _ _ e => by cases e; exact hk.1 rfl) hk.2.1
            (fun e => nomatch e) hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2

/-- **Head expansion** of related terms along typed weak-head reduction. -/
theorem RT.expand (formed : CCtxFormed P Γ) {t : Tok} {T x x' y y' : CTm Head n}
    (rx : CRedTm H Γ x y T) (rx' : CRedTm H Γ x' y' T) (h : RT H Γ true t T y y') :
    RT H Γ true t T x x' :=
  RT.expand_aux levels formed _ t (Nat.lt_succ_self _) _ _ _ _ _ rx rx' h

omit levels in
/-- A term reducing to a normal form at a type, and to another term there, is followed
by the other term to that normal form. -/
theorem CRedTm.reduce_same {a b x T : CTm Head n} (rab : CRedTm H Γ a b T) (rax : CRedTm H Γ a x T)
    (normal : H.Normal x) : CRedTm H Γ b x T :=
  ⟨H.to_normal rax.1 normal rab.1, .trans (.symm rab.2) rax.2⟩

/-- **Head reduction**: terms related at a type as far as a token observes stay
related when either is replaced by a term it reduces to at that type. -/
theorem RT.reduce_aux (formed : CCtxFormed P Γ) : ∀ (N : Nat) (t : Tok), t.depth < N →
    ∀ (T x x' y y' : CTm Head n), CRedTm H Γ x y T → CRedTm H Γ x' y' T →
      RT H Γ true t T x x' → RT H Γ true t T y y'
  | 0, _, hN => absurd hN (Nat.not_lt_zero _)
  | N + 1, t, hN => by
    intro T x x' y y' rx rx' h
    have IH := fun t ht {T x x' y y' : CTm Head n} => RT.reduce_aux formed N t ht T x x' y y'
    cases hv : ent [] t with
    | true => exact RT.of_vacuous hv
    | false =>
    cases htk : typeKind t.kind with
    | true =>
        rcases (RT.tm_type_iff htk).1 h with hvac | ⟨h₀, hu, hT, hr⟩ | ⟨hT, hr⟩
        · exact RT.of_vacuous hvac
        · exact (RT.tm_type_iff htk).2 (.inr (.inl ⟨h₀, hu, hT,
            RT.reduce_ty levels (rx.toTy hu hT) (rx'.toTy hu hT) hr⟩))
        · exact (RT.tm_type_iff htk).2 (.inr (.inr ⟨hT,
            RT.reduce_ty levels (rx.holds hT) (rx'.holds hT) hr⟩))
    | false =>
    have refl : ∀ {B z₁ z₂ r r' : CTm Head n}, ReflRed H Γ T x x' B z₁ z₂ r r' →
        ReflRed H Γ T y y' B z₁ z₂ r r' := fun ⟨hT, r₁, r₂, e₁, e₂, e₃⟩ =>
      ⟨hT, rx.reduce_same r₁ (H.normal_refl _), rx'.reduce_same r₂ (H.normal_refl _), e₁, e₂, e₃⟩
    have succ : ∀ {m m' : CTm Head n}, SuccRed H Γ T x x' m m' → SuccRed H Γ T y y' m m' :=
      fun ⟨hT, r₁, r₂, e⟩ =>
        ⟨hT, rx.reduce_same r₁ (H.normal_suc _), rx'.reduce_same r₂ (H.normal_suc _), e⟩
    have ctor : ∀ {d c : DeclName} {fs : List FieldShape} {ms ms' : List (CTm Head n)},
        CtorRed H Γ d c fs T x x' ms ms' → CtorRed H Γ d c fs T y y' ms ms' :=
      fun ⟨hc, hT, r₁, r₂, fe⟩ => ⟨hc, hT, rx.reduce_same r₁ (H.normal_ctor hc fe.length.1),
        rx'.reduce_same r₂ (H.normal_ctor hc fe.length.2), fe⟩
    have core : ∀ {D : CTm Head n} {E : CTm Head (n + 1)}, CRedTy H Γ T (.sigma D E) →
        CEqual P Γ (.fst x) (.fst x') D → CEqual P Γ (.fst y) (.fst y') D := fun hT e =>
      .trans (.symm (rx.fst hT).2) (.trans e (rx'.fst hT).2)
    cases t with
    | tag k =>
        cases k
        case refl =>
          obtain ⟨B, z₁, z₂, r, r', hr⟩ := RT.tm_reflTag_iff.1 h
          exact RT.tm_reflTag_iff.2 ⟨B, z₁, z₂, r, r', refl hr⟩
        case zero =>
          obtain ⟨hT, r₁, r₂⟩ := RT.tm_zero_iff.1 h
          exact RT.tm_zero_iff.2 ⟨hT, rx.reduce_same r₁ (H.normal_zero),
            rx'.reduce_same r₂ (H.normal_zero)⟩
        case succ =>
          obtain ⟨m, m', hs⟩ := RT.tm_succTag_iff.1 h
          exact RT.tm_succTag_iff.2 ⟨m, m', succ hs⟩
        case pair =>
          exact RT.tm_pairTag_iff.2 fun D E hT => core hT (RT.tm_pairTag_iff.1 h D E hT)
        case ctor d c fs =>
          obtain ⟨ms, ms', hs⟩ := RT.tm_ctorTag_iff.1 h
          exact RT.tm_ctorTag_iff.2 ⟨ms, ms', ctor hs⟩
        all_goals
          exact RT.tm_other htk (fun _ _ _ e => nomatch e)
            (by intro e; cases e) (by intro e; cases e) (by intro e; cases e) (by intro e; cases e)
            (fun _ _ _ e => nomatch e)
    | arg k i C d =>
        rcases kind_cases_tmPair k with rfl | rfl | rfl | rfl | ⟨dn, cn, fs, rfl⟩ | hk
        · exact RT.tm_other htk (fun _ _ _ e => nomatch e) (by intro e; cases e)
            (fun e => nomatch e) (by intro e; cases e) (by intro e; cases e)
            (fun _ _ _ e => nomatch e)
        · rcases RT.tm_argRefl_iff.1 h with hvac | ⟨B, z₁, z₂, r, r', hr, rest⟩
          · exact RT.of_vacuous hvac
          · exact RT.tm_argRefl_iff.2 (.inr ⟨B, z₁, z₂, r, r', refl hr, rest⟩)
        · rcases RT.tm_argSucc_iff.1 h with hvac | ⟨m, m', hs, rest⟩
          · exact RT.of_vacuous hvac
          · exact RT.tm_argSucc_iff.2 (.inr ⟨m, m', succ hs, rest⟩)
        · rcases RT.tm_argPair_iff.1 h with hvac | hcl
          · exact RT.of_vacuous hvac
          refine RT.tm_argPair_iff.2 (.inr fun D E hT => ?_)
          obtain ⟨e₀, hC, h0, h1⟩ := hcl D E hT
          have hE : CIsType P (.snoc Γ D) E :=
            ((CTypeEq.isType levels hT.2 formed).2.sigma_parts).2
          refine ⟨core hT e₀, fun c hc => ?_, fun hi => ?_, fun hi N₁ Q hQ hNQ => ?_⟩
          · have hc' : c.depth < N := by
              have := Tok.depth_lt_of_mem_dep (t := .arg .pair i C d) hc; omega
            exact IH c hc' (rx.fst hT) (rx'.fst hT) (hC c hc)
          · have hd' : d.depth < N := by have := depth_lt_arg .pair i C d; omega
            exact IH d hd' (rx.fst hT) (rx'.fst hT) (h0 hi)
          · have hd' : d.depth < N := by have := depth_lt_arg .pair i C d; omega
            have tx : CTyped P Γ (.fst x) D := (CEqual.typed levels e₀ formed).1
            have exN : CEqual P Γ (.fst x) N₁ D :=
              .trans (rx.fst hT).2 (.trans hQ.2 (.symm hNQ.2))
            exact IH d hd' ((rx.snd hT).retype hE tx exN)
              ((rx'.snd hT).retype hE (CEqual.typed levels e₀ formed).2 (.trans (.symm e₀) exN))
              (h1 hi N₁ Q ((rx.fst hT).trans hQ) hNQ)
        · rcases RT.tm_field_iff.1 h with hvac | ⟨ms, ms', hs, rest⟩
          · exact RT.of_vacuous hvac
          · exact RT.tm_field_iff.2 (.inr ⟨ms, ms', ctor hs, rest⟩)
        · exact RT.tm_other htk (fun _ _ _ e => nomatch e) hk.2.1
            (fun e => nomatch e) hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2
    | fn k C X Y =>
        rcases kind_cases_tmPair k with rfl | rfl | rfl | rfl | ⟨dn, cn, fs, rfl⟩ | hk
        · rcases RT.tm_lam_iff.1 h with hvac | hcl
          · exact RT.of_vacuous hvac
          refine RT.tm_lam_iff.2 (.inr fun D E hT => ?_)
          obtain ⟨hi, hii⟩ := hcl D E hT
          have hE : CIsType P (.snoc Γ D) E :=
            ((CTypeEq.isType levels hT.2 formed).2.pi_parts).2
          refine ⟨fun N₁ N₁' hNN hX y₀ hy₀ => ?_, fun N₁ tN₁ hX y₀ hy₀ => ?_⟩
          · obtain ⟨tN₁, tN₁'⟩ := CEqual.typed levels hNN formed
            have hy₀' : y₀.depth < N := by
              have := depth_lt_fn_right (k := .lam) (C := C) (X := X) hy₀; omega
            obtain ⟨h₁, h₂⟩ := hi N₁ N₁' hNN hX y₀ hy₀
            exact ⟨IH y₀ hy₀' (rx.app hT tN₁) ((rx.app hT tN₁').retype hE tN₁' (.symm hNN)) h₁,
              IH y₀ hy₀' (rx'.app hT tN₁) ((rx'.app hT tN₁').retype hE tN₁' (.symm hNN)) h₂⟩
          · have hy₀' : y₀.depth < N := by
              have := depth_lt_fn_right (k := .lam) (C := C) (X := X) hy₀; omega
            exact IH y₀ hy₀' (rx.app hT tN₁) (rx'.app hT tN₁) (hii N₁ tN₁ hX y₀ hy₀)
        · rcases RT.tm_fnRefl_iff.1 h with hvac | ⟨B, z₁, z₂, r, r', hr, rest⟩
          · exact RT.of_vacuous hvac
          · exact RT.tm_fnRefl_iff.2 (.inr ⟨B, z₁, z₂, r, r', refl hr, rest⟩)
        · rcases RT.tm_fnSucc_iff.1 h with hvac | ⟨m, m', hs, rest⟩
          · exact RT.of_vacuous hvac
          · exact RT.tm_fnSucc_iff.2 (.inr ⟨m, m', succ hs, rest⟩)
        · rcases RT.tm_fnPair_iff.1 h with hvac | hcl
          · exact RT.of_vacuous hvac
          refine RT.tm_fnPair_iff.2 (.inr fun D E hT => ?_)
          obtain ⟨e₀, hC⟩ := hcl D E hT
          refine ⟨core hT e₀, fun c hc => ?_⟩
          have hc' : c.depth < N := by
            have := Tok.depth_lt_of_mem_dep (t := .fn .pair C X Y) hc; omega
          exact IH c hc' (rx.fst hT) (rx'.fst hT) (hC c hc)
        · rcases RT.tm_fnCtor_iff.1 h with hvac | ⟨ms, ms', hs, rest⟩
          · exact RT.of_vacuous hvac
          · exact RT.tm_fnCtor_iff.2 (.inr ⟨ms, ms', ctor hs, rest⟩)
        · exact RT.tm_other htk (fun _ _ _ e => by cases e; exact hk.1 rfl) hk.2.1
            (fun e => nomatch e) hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2

/-- **Head reduction** of related terms along typed weak-head reduction. -/
theorem RT.reduce (formed : CCtxFormed P Γ) {t : Tok} {T x x' y y' : CTm Head n}
    (rx : CRedTm H Γ x y T) (rx' : CRedTm H Γ x' y' T) (h : RT H Γ true t T x x') :
    RT H Γ true t T y y' :=
  RT.reduce_aux levels formed _ t (Nat.lt_succ_self _) _ _ _ _ _ rx rx' h

end Expansion

/-! ## The reflexive instance of the left side -/

section Left

variable {H} {n : Nat} {Γ : CCtx Head n}

theorem RT.left_aux : ∀ (N : Nat) (b : Bool) (t : Tok), 2 * t.depth + b.toNat < N →
    ∀ (T x x' : CTm Head n), RT H Γ b t T x x' → RT H Γ b t T x x
  | 0, _, _, hN => absurd hN (Nat.not_lt_zero _)
  | N + 1, b, t, hN => by
    intro T x x' h
    have IH := RT.left_aux N
    cases hv : ent [] t with
    | true => exact RT.of_vacuous hv
    | false =>
    have sub : ∀ {s : Tok} (b' : Bool), s.depth < t.depth → 2 * s.depth + b'.toNat < N := by
      intro s b' hs
      cases b <;> cases b' <;> simp only [Bool.toNat_false, Bool.toNat_true] at hN ⊢ <;> omega
    have piL : ∀ {D D' : CTm Head n} {E E' : CTm Head (n + 1)}, PiRed H Γ x x' D E D' E' →
        PiRed H Γ x x D E D E := fun ⟨r, _, e, e'⟩ => ⟨r, r, e.left, e'.left⟩
    have idL : ∀ {B z₁ z₂ B' z₁' z₂' : CTm Head n}, IdRed H Γ x x' B z₁ z₂ B' z₁' z₂' →
        IdRed H Γ x x B z₁ z₂ B z₁ z₂ := fun ⟨r, _, e, e₁, e₂⟩ => ⟨r, r, e.left, e₁.left, e₂.left⟩
    have sigmaL : ∀ {D D' : CTm Head n} {E E' : CTm Head (n + 1)},
        SigmaRed H Γ x x' D E D' E' → SigmaRed H Γ x x D E D E :=
      fun ⟨r, _, e, e'⟩ => ⟨r, r, e.left, e'.left⟩
    have dataL : ∀ {d : DeclName}, DataRed H Γ d x x' → DataRed H Γ d x x :=
      fun ⟨hd, r, _⟩ => ⟨hd, r, r⟩
    cases b with
    | false =>
        cases t with
        | tag k =>
            cases k
            case univ =>
              obtain ⟨h₁, _, r₁, _, u₁, _, _⟩ := RT.ty_univ_iff.1 h
              exact RT.ty_univ_iff.2 ⟨h₁, h₁, r₁, r₁, u₁, u₁, .refl _⟩
            case codes =>
              obtain ⟨r₁, _⟩ := RT.ty_codes_iff.1 h
              exact RT.ty_codes_iff.2 ⟨r₁, r₁⟩
            case nat =>
              obtain ⟨r₁, _⟩ := RT.ty_nat_iff.1 h
              exact RT.ty_nat_iff.2 ⟨r₁, r₁⟩
            case pi =>
              obtain ⟨D, E, D', E', hp⟩ := RT.ty_pi_iff.1 h
              exact RT.ty_pi_iff.2 ⟨D, E, D, E, piL hp⟩
            case ident =>
              obtain ⟨B, z₁, z₂, B', z₁', z₂', hi⟩ := RT.ty_ident_iff.1 h
              exact RT.ty_ident_iff.2 ⟨B, z₁, z₂, B, z₁, z₂, idL hi⟩
            case ground =>
              obtain ⟨g, hg, r₁, _⟩ := RT.ty_ground_iff.1 h
              exact RT.ty_ground_iff.2 ⟨g, hg, r₁, r₁⟩
            case sigma =>
              obtain ⟨D, E, D', E', hp⟩ := RT.ty_sigma_iff.1 h
              exact RT.ty_sigma_iff.2 ⟨D, E, D, E, sigmaL hp⟩
            case data d => exact RT.ty_data_iff.2 (dataL (RT.ty_data_iff.1 h))
            all_goals exact RT.ty_tag_other (by simp)
        | arg k i C d =>
            rcases kind_cases_tySigma k with rfl | rfl | rfl | ⟨dn, rfl⟩ | hk
            · rcases RT.ty_argPi_iff.1 h with hvac | ⟨D, E, D', E', hp, hC, hd⟩
              · exact RT.of_vacuous hvac
              · refine RT.ty_argPi_iff.2 (.inr ⟨D, E, D, E, piL hp, fun c hc => ?_, fun hi => ?_⟩)
                · exact IH false c (sub false (Tok.depth_lt_of_mem_dep (t := .arg .pi i C d) hc))
                    _ _ _ (hC c hc)
                · exact IH false d (sub false (depth_lt_arg .pi i C d)) _ _ _ (hd hi)
            · rcases RT.ty_argIdent_iff.1 h with hvac | ⟨B, z₁, z₂, B', z₁', z₂', hi, hC, h0, h1, h2⟩
              · exact RT.of_vacuous hvac
              · refine RT.ty_argIdent_iff.2 (.inr ⟨B, z₁, z₂, B, z₁, z₂, idL hi, fun c hc => ?_,
                  fun e => ?_, fun e => ?_, fun e => ?_⟩)
                · exact IH false c (sub false (Tok.depth_lt_of_mem_dep (t := .arg .ident i C d) hc))
                    _ _ _ (hC c hc)
                · exact IH false d (sub false (depth_lt_arg .ident i C d)) _ _ _ (h0 e)
                · exact IH true d (sub true (depth_lt_arg .ident i C d)) _ _ _ (h1 e)
                · exact IH true d (sub true (depth_lt_arg .ident i C d)) _ _ _ (h2 e)
            · rcases RT.ty_argSigma_iff.1 h with hvac | ⟨D, E, D', E', hp, hC, hd⟩
              · exact RT.of_vacuous hvac
              · refine RT.ty_argSigma_iff.2 (.inr ⟨D, E, D, E, sigmaL hp, fun c hc => ?_,
                  fun hi => ?_⟩)
                · exact IH false c (sub false (Tok.depth_lt_of_mem_dep (t := .arg .sigma i C d) hc))
                    _ _ _ (hC c hc)
                · exact IH false d (sub false (depth_lt_arg .sigma i C d)) _ _ _ (hd hi)
            · rcases RT.ty_param_iff.1 h with hvac | ⟨hd, rest⟩
              · exact RT.of_vacuous hvac
              · exact RT.ty_param_iff.2 (.inr ⟨dataL hd, rest⟩)
            · exact RT.ty_arg_other hk
        | fn k C Z W =>
            rcases kind_cases_tySigma k with rfl | rfl | rfl | ⟨dn, rfl⟩ | hk
            · rcases RT.ty_fnPi_iff.1 h with hvac | ⟨D, E, D', E', hp, hC, hf, -⟩
              · exact RT.of_vacuous hvac
              · refine RT.ty_fnPi_iff.2 (.inr ⟨D, E, D, E, piL hp, fun c hc => ?_,
                  fun N₁ N₁' hNN hZ w hw => ⟨(hf N₁ N₁' hNN hZ w hw).1, (hf N₁ N₁' hNN hZ w hw).1⟩,
                  fun N₁ tN hZ w hw => (hf N₁ N₁ (.refl tN) hZ w hw).1⟩)
                exact IH false c (sub false (Tok.depth_lt_of_mem_dep (t := .fn .pi C Z W) hc))
                  _ _ _ (hC c hc)
            · rcases RT.ty_fnIdent_iff.1 h with hvac | ⟨B, z₁, z₂, B', z₁', z₂', hi, hC⟩
              · exact RT.of_vacuous hvac
              · refine RT.ty_fnIdent_iff.2 (.inr ⟨B, z₁, z₂, B, z₁, z₂, idL hi, fun c hc => ?_⟩)
                exact IH false c (sub false (Tok.depth_lt_of_mem_dep (t := .fn .ident C Z W) hc))
                  _ _ _ (hC c hc)
            · rcases RT.ty_fnSigma_iff.1 h with hvac | ⟨D, E, D', E', hp, hC, hf, -⟩
              · exact RT.of_vacuous hvac
              · refine RT.ty_fnSigma_iff.2 (.inr ⟨D, E, D, E, sigmaL hp, fun c hc => ?_,
                  fun N₁ N₁' hNN hZ w hw => ⟨(hf N₁ N₁' hNN hZ w hw).1, (hf N₁ N₁' hNN hZ w hw).1⟩,
                  fun N₁ tN hZ w hw => (hf N₁ N₁ (.refl tN) hZ w hw).1⟩)
                exact IH false c (sub false (Tok.depth_lt_of_mem_dep (t := .fn .sigma C Z W) hc))
                  _ _ _ (hC c hc)
            · rcases RT.ty_fnData_iff.1 h with hvac | ⟨hd, rest⟩
              · exact RT.of_vacuous hvac
              · exact RT.ty_fnData_iff.2 (.inr ⟨dataL hd, rest⟩)
            · exact RT.ty_fn_other hk
    | true =>
        cases htk : typeKind t.kind with
        | true =>
            have same : 2 * t.depth + false.toNat < N := by
              simp only [Bool.toNat_false, Bool.toNat_true] at hN ⊢; omega
            rcases (RT.tm_type_iff htk).1 h with hvac | ⟨h₀, hu, hT, hr⟩ | ⟨hT, hr⟩
            · exact RT.of_vacuous hvac
            · exact (RT.tm_type_iff htk).2 (.inr (.inl ⟨h₀, hu, hT, IH false t same _ _ _ hr⟩))
            · exact (RT.tm_type_iff htk).2 (.inr (.inr ⟨hT, IH false t same _ _ _ hr⟩))
        | false =>
        have reflL : ∀ {B z₁ z₂ r r' : CTm Head n}, ReflRed H Γ T x x' B z₁ z₂ r r' →
            ReflRed H Γ T x x B z₁ z₂ r r := fun ⟨hT, r₁, _, e₁, e₂, e₃⟩ =>
          ⟨hT, r₁, r₁, e₁, e₂, e₃.left⟩
        have succL : ∀ {m m' : CTm Head n}, SuccRed H Γ T x x' m m' → SuccRed H Γ T x x m m :=
          fun ⟨hT, r₁, _, e⟩ => ⟨hT, r₁, r₁, e.left⟩
        have ctorL : ∀ {d c : DeclName} {fs : List FieldShape} {ms ms' : List (CTm Head n)},
            CtorRed H Γ d c fs T x x' ms ms' → CtorRed H Γ d c fs T x x ms ms :=
          fun ⟨hc, hT, r₁, _, fe⟩ => ⟨hc, hT, r₁, r₁, fe.left⟩
        cases t with
        | tag k =>
            cases k
            case refl =>
              obtain ⟨B, z₁, z₂, r, r', hr⟩ := RT.tm_reflTag_iff.1 h
              exact RT.tm_reflTag_iff.2 ⟨B, z₁, z₂, r, r, reflL hr⟩
            case zero =>
              obtain ⟨hT, r₁, _⟩ := RT.tm_zero_iff.1 h
              exact RT.tm_zero_iff.2 ⟨hT, r₁, r₁⟩
            case succ =>
              obtain ⟨m, m', hs⟩ := RT.tm_succTag_iff.1 h
              exact RT.tm_succTag_iff.2 ⟨m, m, succL hs⟩
            case pair =>
              exact RT.tm_pairTag_iff.2 fun D E hT => (RT.tm_pairTag_iff.1 h D E hT).left
            case ctor d c fs =>
              obtain ⟨ms, ms', hs⟩ := RT.tm_ctorTag_iff.1 h
              exact RT.tm_ctorTag_iff.2 ⟨ms, ms, ctorL hs⟩
            all_goals
              exact RT.tm_other htk (fun _ _ _ e => nomatch e)
                (by intro e; cases e) (by intro e; cases e) (by intro e; cases e)
                (by intro e; cases e) (fun _ _ _ e => nomatch e)
        | arg k i C d =>
            rcases kind_cases_tmPair k with rfl | rfl | rfl | rfl | ⟨dn, cn, fs, rfl⟩ | hk
            · exact RT.tm_other htk (fun _ _ _ e => nomatch e) (by intro e; cases e)
                (fun e => nomatch e) (by intro e; cases e) (by intro e; cases e)
                (fun _ _ _ e => nomatch e)
            · rcases RT.tm_argRefl_iff.1 h with hvac | ⟨B, z₁, z₂, r, r', hr, hC, hd⟩
              · exact RT.of_vacuous hvac
              · refine RT.tm_argRefl_iff.2 (.inr ⟨B, z₁, z₂, r, r, reflL hr, fun c hc => ?_,
                  fun e => ?_⟩)
                · exact ⟨(hC c hc).1, (hC c hc).2.1, IH true c
                    (sub true (Tok.depth_lt_of_mem_dep (t := .arg .refl i C d) hc)) _ _ _
                    (hC c hc).2.2⟩
                · exact ⟨(hd e).1, (hd e).2.1,
                    IH true d (sub true (depth_lt_arg .refl i C d)) _ _ _ (hd e).2.2⟩
            · rcases RT.tm_argSucc_iff.1 h with hvac | ⟨m, m', hs, hC, hd⟩
              · exact RT.of_vacuous hvac
              · refine RT.tm_argSucc_iff.2 (.inr ⟨m, m, succL hs, fun c hc => ?_, fun e => ?_⟩)
                · exact IH true c (sub true (Tok.depth_lt_of_mem_dep (t := .arg .succ i C d) hc))
                    _ _ _ (hC c hc)
                · exact IH true d (sub true (depth_lt_arg .succ i C d)) _ _ _ (hd e)
            · rcases RT.tm_argPair_iff.1 h with hvac | hcl
              · exact RT.of_vacuous hvac
              · refine RT.tm_argPair_iff.2 (.inr fun D E hT => ?_)
                obtain ⟨e₀, hC, h0, h1⟩ := hcl D E hT
                refine ⟨e₀.left, fun c hc => ?_, fun hi => ?_, fun hi N₁ Q hQ hNQ => ?_⟩
                · exact IH true c (sub true (Tok.depth_lt_of_mem_dep (t := .arg .pair i C d) hc))
                    _ _ _ (hC c hc)
                · exact IH true d (sub true (depth_lt_arg .pair i C d)) _ _ _ (h0 hi)
                · exact IH true d (sub true (depth_lt_arg .pair i C d)) _ _ _ (h1 hi N₁ Q hQ hNQ)
            · rcases RT.tm_field_iff.1 h with hvac | ⟨ms, ms', hs, hC, hd⟩
              · exact RT.of_vacuous hvac
              · have hl := hs.2.2.2.2.length
                refine RT.tm_field_iff.2 (.inr ⟨ms, ms, ctorL hs, fun c hc A m m₂ hA => ?_,
                  fun A m m₂ hA => ?_⟩)
                · obtain ⟨rfl, m', hA'⟩ := FieldAt.left (hl.2.trans hl.1.symm) hA
                  exact IH true c (sub true (Tok.depth_lt_of_mem_dep
                    (t := .arg (.ctor dn cn fs) i C d) hc)) _ _ _ (hC c hc A m₂ m' hA')
                · obtain ⟨rfl, m', hA'⟩ := FieldAt.left (hl.2.trans hl.1.symm) hA
                  exact IH true d (sub true (depth_lt_arg (.ctor dn cn fs) i C d)) _ _ _
                    (hd A m₂ m' hA')
            · exact RT.tm_other htk (fun _ _ _ e => nomatch e) hk.2.1
                (fun e => nomatch e) hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2
        | fn k C X Y =>
            rcases kind_cases_tmPair k with rfl | rfl | rfl | rfl | ⟨dn, cn, fs, rfl⟩ | hk
            · rcases RT.tm_lam_iff.1 h with hvac | hcl
              · exact RT.of_vacuous hvac
              · refine RT.tm_lam_iff.2 (.inr fun D E hT => ⟨fun N₁ N₁' hNN hX y hy => ?_,
                  fun N₁ tN hX y hy => ?_⟩)
                · exact ⟨((hcl D E hT).1 N₁ N₁' hNN hX y hy).1,
                    ((hcl D E hT).1 N₁ N₁' hNN hX y hy).1⟩
                · exact ((hcl D E hT).1 N₁ N₁ (.refl tN) hX y hy).1
            · rcases RT.tm_fnRefl_iff.1 h with hvac | ⟨B, z₁, z₂, r, r', hr, hC⟩
              · exact RT.of_vacuous hvac
              · refine RT.tm_fnRefl_iff.2 (.inr ⟨B, z₁, z₂, r, r, reflL hr, fun c hc => ?_⟩)
                exact ⟨(hC c hc).1, (hC c hc).2.1, IH true c
                  (sub true (Tok.depth_lt_of_mem_dep (t := .fn .refl C X Y) hc)) _ _ _
                  (hC c hc).2.2⟩
            · rcases RT.tm_fnSucc_iff.1 h with hvac | ⟨m, m', hs, hC⟩
              · exact RT.of_vacuous hvac
              · refine RT.tm_fnSucc_iff.2 (.inr ⟨m, m, succL hs, fun c hc => ?_⟩)
                exact IH true c (sub true (Tok.depth_lt_of_mem_dep (t := .fn .succ C X Y) hc))
                  _ _ _ (hC c hc)
            · rcases RT.tm_fnPair_iff.1 h with hvac | hcl
              · exact RT.of_vacuous hvac
              · refine RT.tm_fnPair_iff.2 (.inr fun D E hT =>
                  ⟨(hcl D E hT).1.left, fun c hc => ?_⟩)
                exact IH true c (sub true (Tok.depth_lt_of_mem_dep (t := .fn .pair C X Y) hc))
                  _ _ _ ((hcl D E hT).2 c hc)
            · rcases RT.tm_fnCtor_iff.1 h with hvac | ⟨ms, ms', hs, hC⟩
              · exact RT.of_vacuous hvac
              · have hl := hs.2.2.2.2.length
                refine RT.tm_fnCtor_iff.2 (.inr ⟨ms, ms, ctorL hs, fun c hc A m m₂ hA => ?_⟩)
                obtain ⟨rfl, m', hA'⟩ := FieldAt.left (hl.2.trans hl.1.symm) hA
                exact IH true c (sub true (Tok.depth_lt_of_mem_dep
                  (t := .fn (.ctor dn cn fs) C X Y) hc)) _ _ _ (hC c hc A m₂ m' hA')
            · exact RT.tm_other htk (fun _ _ _ e => by cases e; exact hk.1 rfl) hk.2.1
                (fun e => nomatch e) hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2

/-- **The reflexive instance of the left side** of related terms or types. -/
theorem RT.left {b : Bool} {t : Tok} {T x x' : CTm Head n} (h : RT H Γ b t T x x') :
    RT H Γ b t T x x :=
  RT.left_aux _ b t (Nat.lt_succ_self _) T x x' h

end Left

/-! ## Terms of a universe and types -/

section Universes

variable {H} {n : Nat} {Γ : CCtx Head n}

/-- Terms related at a universe are related as types. -/
theorem RT.toType {t : Tok} (htk : typeKind t.kind = true) {T M M' : CTm Head n} {h : Head}
    (hT : CRedTy H Γ T (.head h)) (rel : RT H Γ true t T M M') : RT H Γ false t M M M' := by
  rcases (RT.tm_type_iff htk).1 rel with hvac | ⟨_, _, _, hr⟩ | ⟨hp, _⟩
  · exact RT.of_vacuous hvac
  · exact hr
  · exact (CRedTy.head_ne_prop hT hp).elim

/-- Types related as types are related as terms of a universe. -/
theorem RT.ofType {t : Tok} (htk : typeKind t.kind = true) {T M M' : CTm Head n} {h : Head}
    (hu : R.isUniverse h) (hT : CRedTy H Γ T (.head h)) (rel : RT H Γ false t M M M') :
    RT H Γ true t T M M' :=
  (RT.tm_type_iff htk).2 (.inr (.inl ⟨h, hu, hT, rel⟩))

/-- Codes related at the type of proposition codes have related decodings. -/
theorem RT.toCodes {t : Tok} (htk : typeKind t.kind = true) {T M M' : CTm Head n}
    (hT : CRedTy H Γ T (.const K.prop)) (rel : RT H Γ true t T M M') :
    RT H Γ false t (.app (.const K.holds) M) (.app (.const K.holds) M)
      (.app (.const K.holds) M') := by
  rcases (RT.tm_type_iff htk).1 rel with hvac | ⟨_, _, hh, _⟩ | ⟨_, hr⟩
  · exact RT.of_vacuous hvac
  · exact (CRedTy.head_ne_prop hh hT).elim
  · exact hr

/-- Codes whose decodings are related are related at the type of proposition codes. -/
theorem RT.ofCodes {t : Tok} (htk : typeKind t.kind = true) {T M M' : CTm Head n}
    (hT : CRedTy H Γ T (.const K.prop))
    (rel : RT H Γ false t (.app (.const K.holds) M) (.app (.const K.holds) M)
      (.app (.const K.holds) M')) : RT H Γ true t T M M' :=
  (RT.tm_type_iff htk).2 (.inr (.inr ⟨hT, rel⟩))

end Universes

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
