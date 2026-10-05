import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.DeclarationLists

/-!
# Parameterized datatypes

A datatype may carry a parameter telescope (`Datatype.parameters`). Its type
constant is a function of those parameters, and each constructor and the
recursor take the parameters first. A field is either the datatype at exactly
those parameters (`OpenField.uniform`) or a plain type (`OpenField.plain`).
A plain field may mention the parameters at any position, and it contains no
abstraction. It does not mention the datatype. Positivity restricts the
datatype being defined. `Pred A`, one constructor of a field `A → num`, is
admissible when `num` is a constant other than the datatype (`pred_admissible`).

The empty parameterization is the simple datatype. `parameterDecls` agrees
with `inductiveDecls` there, by computation on the empty telescope, and the
package built by `withDeclarations` is unchanged.

Instantiation at a closed substitution produces a simple datatype whose
constructors are the substituted fields (`Datatype.instantiate`). Substituting
the whole telescope (`subst_dataInstance`) sends the datatype at its parameters
to the datatype at the arguments, outermost first. When the parameterization is
admissible, both universes are universes, the names of the instance are distinct
and new, and a closing substitution is typed, abstraction-free, with each plain
field a type of the datatype's universe, the instance is admissible
(`Datatype.instantiate_admissible`). The names are not part of
`ParameterAdmissible`: a parameterization may be admissible before its names are
chosen.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Normalization
open Mettapedia.TypeTheory.UniverseLevel
open TelescopeAbstraction (closeType)

variable {Head : Type}

/-! ## The datatype at its parameters -/

/-- The parameter arguments, outermost first. In a context of length `p` the
outermost parameter is `var (p - 1)` and the innermost is `var 0`. -/
def paramArgs : (p : Nat) → List (Tm Head p)
  | 0 => []
  | p + 1 => (paramArgs p).map (Presentation.rename wk) ++ [.var 0]

/-- The datatype applied to its parameters. -/
def dataInstance (T : DeclName) (p : Nat) : Tm Head p :=
  appSpine (.const T) (paramArgs p)

@[simp] theorem dataInstance_zero (T : DeclName) :
    dataInstance (Head := Head) T 0 = (.const T : Tm Head 0) := rfl

@[simp] theorem dataInstance_one (T : DeclName) :
    dataInstance (Head := Head) T 1 = (.app (.const T) (.var 0) : Tm Head 1) := rfl

/-- Weaken under `extra` fresh binders. Zero binders leave the term as it is. -/
def weakenBy {n : Nat} : (extra : Nat) → Tm Head n → Tm Head (n + extra)
  | 0, t => t
  | j + 1, t => Presentation.rename wk (weakenBy j t)

/-- The type of a field in the parameter context. -/
def OpenField.term (T : DeclName) {p : Nat} : OpenField Head p → Tm Head p
  | .uniform => dataInstance T p
  | .plain ty => ty

/-- The declared type of a constructor, in the parameter context, under `extra`
field binders already introduced. -/
def ctorOpen (T : DeclName) (p : Nat) : List (OpenField Head p) → (extra : Nat) →
    Tm Head (p + extra)
  | [], extra => weakenBy extra (dataInstance T p)
  | f :: fs, extra =>
      .pi (weakenBy extra (f.term T)) (ctorOpen T p fs (extra + 1))

/-! ## What a plain field may mention -/

/-- The term mentions the constant. -/
def mentionsConst {n : Nat} (c : DeclName) : Tm Head n → Bool
  | .var _ => false
  | .const d => decide (d = c)
  | .head _ => false
  | .pi A B => mentionsConst c A || mentionsConst c B
  | .sigma A B => mentionsConst c A || mentionsConst c B
  | .id A a b => mentionsConst c A || mentionsConst c a || mentionsConst c b
  | .lam body => mentionsConst c body
  | .app f a => mentionsConst c f || mentionsConst c a
  | .pair a b => mentionsConst c a || mentionsConst c b
  | .fst p => mentionsConst c p
  | .snd p => mentionsConst c p
  | .refl a => mentionsConst c a

/-- A plain field is admissible when it does not mention the datatype and it
has no abstraction. A parameter may stand at any position in it. A uniform
field is admissible as written. -/
def plainAdmissible (T : DeclName) {p : Nat} : OpenField Head p → Bool
  | .uniform => true
  | .plain ty => !mentionsConst T ty && lamFree ty

theorem uniform_plainAdmissible (T : DeclName) (p : Nat) :
    plainAdmissible (Head := Head) T (p := p) .uniform = true := rfl

/-- `List (List A)` mentions the datatype, so it is not a plain field. -/
def nestedListField (T : DeclName) : OpenField Head 1 :=
  .plain (.app (.const T) (.app (.const T) (.var 0)))

theorem nestedListField_not_plain (T : DeclName) :
    plainAdmissible (Head := Head) T (nestedListField (Head := Head) T) = false := by
  have mentioned : mentionsConst (Head := Head) T
      (.app (.const T) (.app (.const T) (.var (0 : Fin 1))) : Tm Head 1) = true := by
    simp only [mentionsConst, Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl trivial
  simp only [plainAdmissible, nestedListField, mentioned, Bool.not_true, Bool.false_and]

/-- The field `A → num`. The parameter stands in the domain. -/
def predField (numN : DeclName) : OpenField Head 1 :=
  .plain (.pi (.var 0) (.const numN))

theorem predField_plain (T numN : DeclName) (fresh : T ≠ numN) :
    plainAdmissible (Head := Head) T (predField (Head := Head) numN) = true := by
  have quiet : mentionsConst (Head := Head) T
      (.pi (.var (0 : Fin 1)) (.const numN) : Tm Head 1) = false := by
    simp only [mentionsConst, Bool.false_or]
    exact decide_eq_false (Ne.symm fresh)
  simp only [plainAdmissible, predField, quiet, Bool.not_false, lamFree, Bool.and_self]

/-! ## The recursor, parameters first -/

/-- The type `List A → v` of a motive, in the parameter context. -/
def motiveOpen (T : DeclName) (v : Head) (p : Nat) : Tm Head p :=
  .pi (dataInstance T p) (.head v)

/-- A term of the parameter context, under the motive and `extra` further binders. -/
def underMotive {p : Nat} (t : Tm Head p) (extra : Nat) : Tm Head ((p + 1) + extra) :=
  weakenBy extra (Presentation.rename wk t)

/-- The motive, after `done` field binders. -/
def motiveAt (p done : Nat) : Tm Head ((p + 1) + done) :=
  .var ⟨done, by omega⟩

/-- `k` applied to the `done` field binders, leftmost field first. -/
def ctorSpine {m : Nat} (k : DeclName) (done : Nat) (enough : done ≤ m) : Tm Head m :=
  appSpine (.const k) ((List.finRange done).map fun i =>
    .var ⟨done - 1 - i.val, by omega⟩)

/-- The variables of the uniform fields, leftmost field first, among `done` field binders. -/
def recursiveVars {p m : Nat} (fields : List (OpenField Head p)) (done : Nat)
    (_enough : done ≤ m) : List (Tm Head m) :=
  go fields 0
where
  go : List (OpenField Head p) → Nat → List (Tm Head m)
    | [], _ => []
    | .uniform :: fs, i =>
        if h : i < done then
          .var ⟨done - 1 - i, by omega⟩ :: go fs (i + 1)
        else
          go fs (i + 1)
    | .plain _ :: fs, i => go fs (i + 1)

/-- Induction hypotheses `P r → ⋯ → P target`, read under `extra` binders. -/
def ihThen {m : Nat} (motive target : Tm Head m) : List (Tm Head m) → (extra : Nat) →
    Tm Head (m + extra)
  | [], extra => .app (weakenBy extra motive) (weakenBy extra target)
  | r :: rs, extra =>
      .pi (.app (weakenBy extra motive) (weakenBy extra r))
        (ihThen motive target rs (extra + 1))

/-- The method of constructor `k`: its fields, an induction hypothesis for each
uniform field, and the motive at the constructed value. -/
def methodEnd (k : DeclName) (p : Nat) (fields : List (OpenField Head p)) (done : Nat) :
    Tm Head ((p + 1) + done) :=
  ihThen (motiveAt p done) (ctorSpine k done (by omega))
    (recursiveVars fields done (by omega)) 0

def methodBody (T k : DeclName) (p : Nat) (fields : List (OpenField Head p)) :
    List (OpenField Head p) → (done : Nat) → Tm Head ((p + 1) + done)
  | [], done => methodEnd k p fields done
  | f :: fs, done =>
      .pi (underMotive (f.term T) done) (methodBody T k p fields fs (done + 1))

/-- The method, in the context where the motive is the newest variable. -/
def methodOpen (T k : DeclName) (p : Nat) (fields : List (OpenField Head p)) :
    Tm Head (p + 1) :=
  methodBody T k p fields fields 0

/-- The methods and the scrutinee, in that same context. -/
def methodsFrom (T : DeclName) (p : Nat) :
    List (DeclName × List (OpenField Head p)) → Tm Head (p + 1)
  | [] =>
      .pi (Presentation.rename wk (dataInstance T p))
        (.app (Presentation.rename wk (.var (0 : Fin (p + 1)))) (.var 0))
  | (k, fields) :: rest =>
      .pi (methodOpen T k p fields) (Presentation.rename wk (methodsFrom T p rest))

/-- The declared type of the recursor in the parameter context. -/
def recOpen (T : DeclName) (v : Head) (p : Nat)
    (ctors : List (DeclName × List (OpenField Head p))) : Tm Head p :=
  .pi (motiveOpen T v p) (methodsFrom T p ctors)

/-! ## Declared types -/

/-- The declared types of a datatype. The empty parameterization is
`inductiveDecls` of the simple constructors. -/
def parameterDecls (d : Datatype Head) : DeclName → Option (Tm Head 0) :=
  if d.parameters.telescope.count == 0 && d.parameters.constructors.isEmpty then
    inductiveDecls d.type d.typeUniverse d.ctors d.recursor d.motiveUniverse
  else fun name =>
    let tele := d.parameters.telescope.context
    let p := d.parameters.telescope.count
    let openCtors := d.parameters.constructors
    if name = d.type then some (closeType tele (.head d.typeUniverse))
    else match openCtors.find? (fun entry => entry.1 = name) with
      | some entry => some (closeType tele (ctorOpen d.type p entry.2 0))
      | none =>
          if name = d.recursor then
            some (closeType tele (recOpen d.type d.motiveUniverse p openCtors))
          else none

/-- The declared type of the type constant. -/
def typeConstant (d : Datatype Head) : Tm Head 0 :=
  closeType d.parameters.telescope.context (.head d.typeUniverse)

theorem parameterDecls_of_none (d : Datatype Head) (h : d.parameters = .none) :
    parameterDecls d =
      inductiveDecls d.type d.typeUniverse d.ctors d.recursor d.motiveUniverse := by
  cases d
  cases h
  rfl

theorem typeConstant_of_none (d : Datatype Head) (h : d.parameters = .none) :
    typeConstant d = .head d.typeUniverse := by
  unfold typeConstant
  rw [h]
  rfl

/-- Substituting one closed argument for the single parameter sends the datatype
at that parameter to the datatype at the argument. -/
theorem subst_dataInstance_one (T : DeclName) (a : Tm Head 0) :
    Presentation.subst (fun _ : Fin 1 => a) (dataInstance T 1) = .app (.const T) a := rfl

/-- The arguments of a substitution, outermost parameter first. -/
def substParams : {p m : Nat} → Sub Head p m → List (Tm Head m)
  | 0, _, _ => []
  | _ + 1, _, σ => substParams (tailSub σ) ++ [σ 0]

theorem map_subst_rename_wk {p m : Nat} (σ : Sub Head (p + 1) m)
    (ts : List (Tm Head p)) :
    (ts.map (Presentation.rename wk)).map (Presentation.subst σ) =
      ts.map (Presentation.subst (tailSub σ)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons]
    rw [subst_rename_wk, ih]

/-- Substitution sends the parameter arguments to the arguments of the
substitution, outermost first. -/
theorem map_subst_paramArgs {p m : Nat} (σ : Sub Head p m) :
    (paramArgs p).map (Presentation.subst σ) = substParams σ := by
  induction p generalizing m with
  | zero => rfl
  | succ p ih =>
    rw [paramArgs, substParams]
    simp only [List.map_append, List.map_cons, List.map_nil, subst_var]
    rw [map_subst_rename_wk, ih]

/-- Substituting closed arguments for every parameter sends the datatype at
those parameters to the datatype at the arguments, outermost first. -/
theorem subst_dataInstance {p : Nat} (T : DeclName) (σ : Sub Head p 0) :
    Presentation.subst σ (dataInstance T p) =
      appSpine (.const T) (substParams σ) := by
  unfold dataInstance
  rw [subst_appSpine, map_subst_paramArgs]
  rfl

/-- Lifting a substitution of abstraction-free terms keeps every image
abstraction-free. The new variable is a variable. -/
theorem lamFree_liftSub {n m : Nat} (σ : Sub Head n m)
    (images : ∀ i, lamFree (σ i) = true) (i : Fin (n + 1)) :
    lamFree (Presentation.liftSub σ i) = true := by
  refine Fin.cases ?_ ?_ i
  · rw [liftSub_zero]
    rfl
  · intro j
    rw [liftSub_succ, lamFree_rename]
    exact images j

/-- Substitution of abstraction-free terms into an abstraction-free term is
abstraction-free. -/
theorem lamFree_subst :
    ∀ {n m : Nat} (σ : Sub Head n m) (t : Tm Head n),
      lamFree t = true → (∀ i, lamFree (σ i) = true) →
        lamFree (Presentation.subst σ t) = true
  | _, _, _, .var i, _, images => images i
  | _, _, _, .const _, _, _ => rfl
  | _, _, _, .head _, _, _ => rfl
  | _, _, σ, .pi A B, free, images => by
      simp only [lamFree, Bool.and_eq_true] at free
      show (lamFree (Presentation.subst σ A) &&
          lamFree (Presentation.subst (Presentation.liftSub σ) B)) = true
      rw [lamFree_subst σ A free.1 images,
        lamFree_subst (Presentation.liftSub σ) B free.2 (lamFree_liftSub σ images)]
      rfl
  | _, _, σ, .sigma A B, free, images => by
      simp only [lamFree, Bool.and_eq_true] at free
      show (lamFree (Presentation.subst σ A) &&
          lamFree (Presentation.subst (Presentation.liftSub σ) B)) = true
      rw [lamFree_subst σ A free.1 images,
        lamFree_subst (Presentation.liftSub σ) B free.2 (lamFree_liftSub σ images)]
      rfl
  | _, _, σ, .id A a b, free, images => by
      simp only [lamFree, Bool.and_eq_true] at free
      have freeLeft : lamFree A = true ∧ lamFree a = true := by
        exact free.1
      show (lamFree (Presentation.subst σ A) && lamFree (Presentation.subst σ a) &&
          lamFree (Presentation.subst σ b)) = true
      rw [lamFree_subst σ A freeLeft.1 images, lamFree_subst σ a freeLeft.2 images,
        lamFree_subst σ b free.2 images]
      rfl
  | _, _, _, .lam _, free, _ => by
      simp only [lamFree] at free
      cases free
  | _, _, σ, .app f a, free, images => by
      simp only [lamFree, Bool.and_eq_true] at free
      show (lamFree (Presentation.subst σ f) && lamFree (Presentation.subst σ a)) = true
      rw [lamFree_subst σ f free.1 images, lamFree_subst σ a free.2 images]
      rfl
  | _, _, σ, .pair a b, free, images => by
      simp only [lamFree, Bool.and_eq_true] at free
      show (lamFree (Presentation.subst σ a) && lamFree (Presentation.subst σ b)) = true
      rw [lamFree_subst σ a free.1 images, lamFree_subst σ b free.2 images]
      rfl
  | _, _, σ, .fst p, free, images => by
      show lamFree (Presentation.subst σ p) = true
      rw [lamFree] at free
      exact lamFree_subst σ p free images
  | _, _, σ, .snd p, free, images => by
      show lamFree (Presentation.subst σ p) = true
      rw [lamFree] at free
      exact lamFree_subst σ p free images
  | _, _, σ, .refl a, free, images => by
      show lamFree (Presentation.subst σ a) = true
      rw [lamFree] at free
      exact lamFree_subst σ a free images

/-! ## Admissibility of a telescope -/

variable {R : Rules Head}

/-- The parameter telescope is formed. The empty telescope is formed. -/
def TelescopeFormed (B : ChurchRules R) : {n : Nat} → Ctx Head n → Prop
  | _, .nil => True
  | _, .snoc prior domain =>
      TelescopeFormed B prior ∧ CIsType B (liftCtx prior) (liftTm domain)

/-- A parameterization is admissible over a package: its telescope is formed,
every plain field passes `plainAdmissible`, and the open constructors and the
simple constructors are not both present. -/
structure ParameterAdmissible (B : ChurchRules R) (d : Datatype Head) : Prop where
  telescope : TelescopeFormed B d.parameters.telescope.context
  fields : ∀ {k : DeclName} {fs : List (OpenField Head d.parameters.telescope.count)},
    (k, fs) ∈ d.parameters.constructors → ∀ f ∈ fs,
      plainAdmissible d.type f = true
  exclusive : d.parameters.constructors = [] ∨ d.ctors = []

/-- The empty parameterization is admissible over every package. -/
theorem ParameterAdmissible.of_none {B : ChurchRules R} {d : Datatype Head}
    (h : d.parameters = .none) : ParameterAdmissible B d := by
  cases d
  cases h
  refine ⟨trivial, ?_, Or.inl rfl⟩
  intro _ _ member _ _
  cases member

theorem not_parameterAdmissible_of_plain {B : ChurchRules R} {d : Datatype Head}
    {k : DeclName} {fs : List (OpenField Head d.parameters.telescope.count)}
    {f : OpenField Head d.parameters.telescope.count}
    (member : (k, fs) ∈ d.parameters.constructors) (fm : f ∈ fs)
    (bad : plainAdmissible d.type f = false) : ¬ ParameterAdmissible B d := by
  intro adm
  have got := adm.fields member f fm
  rw [bad] at got
  cases got

/-- A constructor whose field is `List (List A)` is not admissible. -/
def nestedListData (T recName : DeclName) (u v : Head) : Datatype Head where
  type := T
  typeUniverse := u
  ctors := []
  recursor := recName
  motiveUniverse := v
  parameters := {
    telescope := ⟨1, .snoc .nil (.head u)⟩
    constructors := [(recName, [nestedListField T])]
  }

theorem nestedList_not_admissible {B : ChurchRules R} (T recName : DeclName) (u v : Head) :
    ¬ ParameterAdmissible B (nestedListData T recName u v) := by
  refine not_parameterAdmissible_of_plain (d := nestedListData T recName u v)
    (k := recName) (fs := [nestedListField T]) (f := nestedListField T) ?_ ?_
    (nestedListField_not_plain T)
  · exact List.mem_cons_self
  · exact List.mem_cons_self

/-- `Pred A`: one parameter, and one constructor whose field is `A → num`. -/
def predData (predN mkN recN numN : DeclName) (u v : Head) : Datatype Head where
  type := predN
  typeUniverse := u
  ctors := []
  recursor := recN
  motiveUniverse := v
  parameters := {
    telescope := ⟨1, .snoc .nil (.head u)⟩
    constructors := [(mkN, [predField numN])]
  }

/-- `Pred A` is admissible. The parameter is a type because `u` is a universe of
the package, and the field `A → num` mentions a parameter in its domain. -/
theorem pred_admissible {L : Type} [LevelOrder L] {R : Rules Head} {B : ChurchRules R}
    (levels : LevelModel R L) (predN mkN recN numN : DeclName) (u v : Head)
    (hu : R.isUniverse u) (fresh : predN ≠ numN) :
    ParameterAdmissible B (predData predN mkN recN numN u v) := by
  refine ⟨⟨trivial, ?_⟩, ?_, Or.inr rfl⟩
  · exact CIsType.head_of_universe (P := B) (Γ := .nil) levels hu
  · intro k fs member f fm
    have ctor : (k, fs) = (mkN, [predField (Head := Head) numN]) :=
      List.mem_singleton.mp (by simpa [predData] using member)
    cases ctor
    have field : f = predField (Head := Head) numN := List.mem_singleton.mp fm
    cases field
    exact predField_plain predN numN fresh

/-! ## Two closed parameters -/

theorem const_ne_app {n : Nat} {c : DeclName} {f a : Tm Head n} :
    (.const c : Tm Head n) ≠ .app f a := by
  intro eq
  cases eq

theorem applied_const_ne {n : Nat} {c : DeclName} {a b : Tm Head n} (h : a ≠ b) :
    Tm.app (.const c) a ≠ .app (.const c) b := by
  intro eq
  apply h
  cases eq
  rfl

/-- `List num` and `List (List num)` are different types. -/
theorem listNum_ne_listList (numN listN : DeclName) :
    (Tm.app (.const listN) (.const numN) : Tm Head 0) ≠
      .app (.const listN) (.app (.const listN) (.const numN)) :=
  applied_const_ne (const_ne_app (c := numN) (f := .const listN) (a := .const numN))

/-- `nil num` and `nil (List num)` are different terms, and the previous theorem
says the types they are built at are different, so the two are not one term at
one type. -/
theorem nilNum_ne_nilList (numN listN nilN : DeclName) :
    (Tm.app (.const nilN) (.const numN) : Tm Head 0) ≠
      .app (.const nilN) (.app (.const listN) (.const numN)) :=
  applied_const_ne (const_ne_app (c := numN) (f := .const listN) (a := .const numN))

/-! ## Instantiation -/

/-- A field at a closed substitution of its parameters. A uniform field is the
simple recursive field. -/
def OpenField.instantiate {p : Nat} (σ : Sub Head p 0) : OpenField Head p → Field Head
  | .uniform => .recursive
  | .plain t => .closed (Presentation.subst σ t)

/-- The simple datatype at a closed substitution of the parameters. Its
constructors are the substituted open constructors. A simple datatype is already
that instance; this reads the open constructors. -/
def Datatype.instantiate (d : Datatype Head)
    (σ : Sub Head d.parameters.telescope.count 0) : Datatype Head where
  type := d.type
  typeUniverse := d.typeUniverse
  ctors := d.parameters.constructors.map fun entry =>
    (entry.1, entry.2.map (OpenField.instantiate σ))
  recursor := d.recursor
  motiveUniverse := d.motiveUniverse
  parameters := .none

theorem Datatype.instantiate_parameters (d : Datatype Head)
    (σ : Sub Head d.parameters.telescope.count 0) :
    (d.instantiate σ).parameters = .none := rfl

theorem Datatype.instantiate_ctors (d : Datatype Head)
    (σ : Sub Head d.parameters.telescope.count 0) :
    (d.instantiate σ).ctors =
      d.parameters.constructors.map fun entry =>
        (entry.1, entry.2.map (OpenField.instantiate σ)) := rfl

/-- A closed instance of an admissible parameterization is an admissible simple
datatype. `ParameterAdmissible` supplies the telescope and the plain fields. The
two universes, the distinctness and newness of the instance's names, and the
typing of the closing substitution and of each plain field are further data:
a parameterization may be admissible before its names are chosen. -/
theorem Datatype.instantiate_admissible {B : ChurchRules R} {d : Datatype Head}
    {σ : Sub Head d.parameters.telescope.count 0}
    (param : ParameterAdmissible B d)
    (typeU : R.isUniverse d.typeUniverse)
    (motiveU : R.isUniverse d.motiveUniverse)
    (distinct : DistinctNames d.type (d.instantiate σ).ctors d.recursor)
    (fresh : NewNames B d.type (d.instantiate σ).ctors d.recursor)
    (closed : ∀ i, lamFree (σ i) = true)
    (mor : CSubstMor B (liftCtx d.parameters.telescope.context) .nil
      (fun i => liftTm (σ i)))
    (hPlain : ∀ {k : DeclName} {fs : List (OpenField Head d.parameters.telescope.count)}
      {ty : Tm Head d.parameters.telescope.count},
      (k, fs) ∈ d.parameters.constructors → .plain ty ∈ fs →
      CTyped B (liftCtx d.parameters.telescope.context) (liftTm ty)
        (.head d.typeUniverse)) :
    (d.instantiate σ).Admissible B where
  typeUniverse := typeU
  motiveUniverse := motiveU
  distinct := distinct
  new := fresh
  lamFree := by
    intro entry member F field
    rw [Datatype.instantiate_ctors] at member
    obtain ⟨⟨k, fs⟩, memOpen, rfl⟩ := List.mem_map.mp member
    obtain ⟨f, fm, hf⟩ := List.mem_map.mp field
    cases f with
    | uniform =>
      simp only [OpenField.instantiate] at hf
      cases hf
    | plain ty =>
      simp only [OpenField.instantiate] at hf
      cases hf
      have admissible := param.fields memOpen (.plain ty) fm
      have freeTy : lamFree ty = true := by
        simp only [plainAdmissible, Bool.and_eq_true] at admissible
        exact admissible.2
      exact lamFree_subst σ ty freeTy closed
  fields := by
    intro entry member F field
    rw [Datatype.instantiate_ctors] at member
    obtain ⟨⟨k, fs⟩, memOpen, rfl⟩ := List.mem_map.mp member
    obtain ⟨f, fm, hf⟩ := List.mem_map.mp field
    cases f with
    | uniform =>
      simp only [OpenField.instantiate] at hf
      cases hf
    | plain ty =>
      simp only [OpenField.instantiate] at hf
      cases hf
      have got := (hPlain memOpen fm).substitute mor
      rw [← liftTm_subst σ ty] at got
      exact got

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
