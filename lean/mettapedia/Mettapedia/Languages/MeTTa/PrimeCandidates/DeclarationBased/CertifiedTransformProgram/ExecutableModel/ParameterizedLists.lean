import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConstructorView
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.DataAlgorithmic
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ParameterizedDatatypes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ParameterizedPackage

/-!
# Every closed instance, in the object package

`listOpen` is lists with one parameter, at the least universe of the object
calculus. `listAt A` is that datatype instantiated at a closed type `A`. Every
closed instance of an admissible parameterization is an admissible simple
datatype (`Datatype.instantiate_admissible`), so strong normalization
(`instance_sn`), canonicity (`instance_canonical`), conversion completeness
(`instance_algorithmicComplete`) and the refutation of two different
constructors (`instance_ctor_not_equal`) hold there. The list theorems are
those facts at `List A`. Cite `listAt_nil_ne_cons` for `nil` against `cons`
at `List A`.

`Pair A B` is two parameters (`pairAt_admissible`). `Pred A` puts its parameter
in the domain of a field (`predAt_admissible`). `List zero` is not an
admissible instance (`listAt_zero_not_admissible`).

The list names are `list`, `nil`, `cons` and `list-rec`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.StrongNormalization
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Annotated

namespace CodeModel

/-- One parameter, a type of the least universe. `nil` has no fields. `cons` has
the parameter and one uniform field. -/
def listParameter : Parameterization Tower.Head where
  telescope := ⟨1, .snoc .nil (.head (.sort Tower.zero))⟩
  constructors := [(nilN, []), (consN, [.plain (.var 0), .uniform])]

/-- Lists with one parameter. The constructors are the open fields. -/
def listOpen : Datatype Tower.Head where
  type := listN
  typeUniverse := .sort Tower.zero
  ctors := []
  recursor := listRecN
  motiveUniverse := listMotives
  parameters := listParameter

/-- `List A`, the simple datatype at the closed type `A`. -/
def listAt (A : Tm Tower.Head 0) : Datatype Tower.Head :=
  listOpen.instantiate (fun _ => A)

@[simp] theorem listAt_ctors (A : Tm Tower.Head 0) :
    (listAt A).ctors = [(nilN, []), (consN, [.closed A, .recursive])] := rfl

/-- The names of `List A` are the names of the lists of numbers, so they avoid
the names the value side reserves. -/
theorem listAt_avoids (A : Tm Tower.Head 0) : AvoidsModelNames (listAt A) := by
  intro c mem
  have names : dataNames (listAt A) = dataNames listDecl := by
    simp only [dataNames, listAt, Datatype.instantiate, listOpen, listParameter, listDecl,
      listCtors, List.map_cons, List.map_nil]
  exact listDecl_avoids c (names ▸ mem)

/-- The open list declaration is an admissible parameterization. Its one
parameter is a type of the least universe. -/
theorem listOpen_admissible : ParameterAdmissible objectChurch listOpen where
  telescope := ⟨trivial, CIsType.head_of_universe (P := objectChurch) (Γ := .nil)
    ConvRules.objectLevels (LevelTower.IsUniverse.sort _)⟩
  fields := by
    intro k fs member f fm
    dsimp [listOpen, listParameter] at member fm
    cases List.mem_cons.mp member with
    | inl eq =>
      cases eq
      cases fm
    | inr rest =>
      cases List.mem_cons.mp rest with
      | inl eq =>
        cases eq
        cases List.mem_cons.mp fm with
        | inl eq =>
          cases eq
          rfl
        | inr rest =>
          cases List.mem_cons.mp rest with
          | inl eq =>
            cases eq
            rfl
          | inr rest => cases rest
      | inr rest => cases rest
  exclusive := Or.inr rfl

/-- The closing substitution at one typed parameter. -/
theorem listAt_mor {A : Tm Tower.Head 0}
    (typed : CTyped objectChurch .nil (liftTm A) (.head (.sort Tower.zero))) :
    CSubstMor objectChurch (liftCtx listOpen.parameters.telescope.context) .nil
      (fun _ => liftTm A) := by
  intro i
  dsimp [listOpen, listParameter, liftCtx] at i ⊢
  obtain rfl : i = 0 := Subsingleton.elim i 0
  exact typed

/-- Each plain field of the open lists is a type of the least universe in the
parameter context. The one plain field is the parameter. -/
theorem listAt_plain {k : DeclName} {fs : List (OpenField Tower.Head 1)}
    {ty : Tm Tower.Head 1}
    (member : (k, fs) ∈ listOpen.parameters.constructors) (fm : .plain ty ∈ fs) :
    CTyped objectChurch (liftCtx listOpen.parameters.telescope.context) (liftTm ty)
      (.head (.sort Tower.zero)) := by
  dsimp [listOpen, listParameter, liftCtx] at member fm ⊢
  cases List.mem_cons.mp member with
  | inl eq =>
    cases eq
    cases fm
  | inr rest =>
    cases List.mem_cons.mp rest with
    | inl eq =>
      cases eq
      cases List.mem_cons.mp fm with
      | inl eq =>
        injection eq with h
        cases h
        exact .var 0
      | inr rest =>
        cases List.mem_cons.mp rest with
        | inl eq => cases eq
        | inr rest => cases rest
    | inr rest => cases rest

/-- `List A` is admissible over the object package when `A` is a type of the
least universe and contains no abstraction. -/
theorem listAt_admissible {A : Tm Tower.Head 0}
    (typed : CTyped objectChurch .nil (liftTm A) (.head (.sort Tower.zero)))
    (free : lamFree A = true) : (listAt A).Admissible objectChurch :=
  Datatype.instantiate_admissible (d := listOpen) (σ := fun _ => A) listOpen_admissible
    (LevelTower.IsUniverse.sort _) (LevelTower.IsUniverse.sort _)
    { ctorsNodup := by
        show ([nilN, consN] : List DeclName).Nodup
        decide
      typeNotCtor := by
        show listN ∉ [nilN, consN]
        decide
      recNotType := by decide
      recNotCtor := by
        show listRecN ∉ [nilN, consN]
        decide }
    { typeNew := lists_new.typeNew
      recNew := lists_new.recNew
      ctorsNew := by
        intro entry member
        rw [show (listOpen.instantiate (fun _ => A)).ctors =
            [(nilN, []), (consN, [.closed A, .recursive])] from listAt_ctors A] at member
        cases List.mem_cons.mp member with
        | inl eq =>
          cases eq
          exact lists_new.ctorsNew (nilN, []) List.mem_cons_self
        | inr rest =>
          cases List.mem_cons.mp rest with
          | inl eq =>
            cases eq
            exact lists_new.ctorsNew (consN, [.closed (.const numN), .recursive])
              (List.mem_cons_of_mem (nilN, []) List.mem_cons_self)
          | inr rest => cases rest }
    (fun i => by
      dsimp [listOpen, listParameter] at i
      obtain rfl : i = 0 := Subsingleton.elim i 0
      exact free)
    (listAt_mor typed) listAt_plain

/-! ## The simple theorems at every closed instance -/

/-- **Strong normalization at a closed instance.** -/
theorem instance_sn {d : Datatype Tower.Head}
    {σ : Sub Tower.Head d.parameters.telescope.count 0}
    (hd : (d.instantiate σ).Admissible objectChurch)
    (avoid : AvoidsModelNames (d.instantiate σ)) {n : Nat} {Γ : Tower.Ctx n}
    {t B : Tower.Tm n} (formed : CtxFormed (dataRules (d.instantiate σ)) Γ)
    (term : Typed (dataRules (d.instantiate σ)) Γ t B) :
    SN (dataRules (d.instantiate σ)) t ∧ SN (dataRules (d.instantiate σ)) B :=
  dataRules_sn hd avoid formed term

/-- **Canonicity at a closed instance.** A closed term typed at the instance
weak-head reduces to a listed constructor. -/
theorem instance_canonical {d : Datatype Tower.Head}
    {σ : Sub Tower.Head d.parameters.telescope.count 0}
    (hd : (d.instantiate σ).Admissible objectChurch)
    (avoid : AvoidsModelNames (d.instantiate σ)) {t : CTm Tower.Head 0}
    (atType : CTyped (dataChurch (d.instantiate σ)) .nil t
      (.const (d.instantiate σ).type)) :
    ∃ (i : Nat) (k : DeclName) (fs : List CtorField) (args : List (CTm Tower.Head 0)),
      (d.instantiate σ).ctors[i]? = some (k, fs) ∧ args.length = fs.length ∧
      List.Forall₂ (fun a (f : CtorField) =>
        CTyped (dataChurch (d.instantiate σ)) .nil a
          (liftTm (f.type (d.instantiate σ).type)).liftClosed) args fs ∧
      CRedTm (dataHead hd) .nil t (CTm.appSpine (.const k) args)
        (.const (d.instantiate σ).type) :=
  data_canonical hd avoid atType

/-- **Conversion completeness at a closed instance.** -/
theorem instance_algorithmicComplete {d : Datatype Tower.Head}
    {σ : Sub Tower.Head d.parameters.telescope.count 0}
    (hd : (d.instantiate σ).Admissible objectChurch)
    (avoid : AvoidsModelNames (d.instantiate σ)) :
    AlgorithmicComplete (dataRules (d.instantiate σ)) (dataRoles (d.instantiate σ)) :=
  ConvRules.dataRules_algorithmicComplete hd avoid

/-- **A refutation by the algorithm at a closed instance.** Two terms of a
principal type that the conversion algorithm does not relate there are equal
at no type. -/
theorem instance_not_equal_of_unrelated {d : Datatype Tower.Head}
    {σ : Sub Tower.Head d.parameters.telescope.count 0}
    (hd : (d.instantiate σ).Admissible objectChurch)
    (avoid : AvoidsModelNames (d.instantiate σ)) {n : Nat} {Γ : Tower.Ctx n}
    {t u T C : Tower.Tm n} (formed : CtxFormed (dataRules (d.instantiate σ)) Γ)
    (tT : Typed (dataRules (d.instantiate σ)) Γ t T)
    (uT : Typed (dataRules (d.instantiate σ)) Γ u T)
    (principal : ∀ {X}, Typed (dataRules (d.instantiate σ)) Γ t X →
      TypeLe (dataRules (d.instantiate σ)) Γ T X)
    (unrelated : ¬ Algorithmic (dataRules (d.instantiate σ))
      (dataRoles (d.instantiate σ)) (.terms Γ t u T)) :
    ¬ Equal (dataRules (d.instantiate σ)) Γ t u C :=
  ConvRules.dataRules_not_equal_of_unrelated hd avoid formed tT uT principal unrelated

/-- **Two different constructors of a closed instance are never equal.** Closed
applications of different constructors, with any arguments, are not equal at
the instance. -/
theorem instance_ctor_not_equal {d : Datatype Tower.Head}
    {σ : Sub Tower.Head d.parameters.telescope.count 0}
    (hd : (d.instantiate σ).Admissible objectChurch) {i j : Nat} {k k' : DeclName}
    {fs fs' : List CtorField} (hi : (d.instantiate σ).ctors[i]? = some (k, fs))
    (hj : (d.instantiate σ).ctors[j]? = some (k', fs')) (ne : k ≠ k')
    (args args' : List (CTm Tower.Head 0)) :
    ¬ CEqual (dataChurch (d.instantiate σ)) .nil (CTm.appSpine (.const k) args)
      (CTm.appSpine (.const k') args') (.const (d.instantiate σ).type) :=
  ctor_not_equal_ctor hd hi hj ne args args'

/-- **Strong normalization at `List A`.** A term typed in a formed context of the
package, and its type, are strongly normalizing. -/
theorem listAt_sn {A : Tm Tower.Head 0}
    (typed : CTyped objectChurch .nil (liftTm A) (.head (.sort Tower.zero)))
    (free : lamFree A = true) {n : Nat} {Γ : Tower.Ctx n} {t B : Tower.Tm n}
    (formed : CtxFormed (dataRules (listAt A)) Γ)
    (term : Typed (dataRules (listAt A)) Γ t B) :
    SN (dataRules (listAt A)) t ∧ SN (dataRules (listAt A)) B :=
  instance_sn (listAt_admissible typed free) (listAt_avoids A) formed term

/-- **Canonicity at `List A`.** A closed term typed at `List A` weak-head reduces
to a listed constructor. -/
theorem listAt_canonical {A : Tm Tower.Head 0}
    (typed : CTyped objectChurch .nil (liftTm A) (.head (.sort Tower.zero)))
    (free : lamFree A = true) {t : CTm Tower.Head 0}
    (atType : CTyped (dataChurch (listAt A)) .nil t (.const (listAt A).type)) :
    ∃ (i : Nat) (k : DeclName) (fs : List CtorField) (args : List (CTm Tower.Head 0)),
      (listAt A).ctors[i]? = some (k, fs) ∧ args.length = fs.length ∧
      List.Forall₂ (fun a (f : CtorField) =>
        CTyped (dataChurch (listAt A)) .nil a
          (liftTm (f.type (listAt A).type)).liftClosed) args fs ∧
      CRedTm (dataHead (listAt_admissible typed free)) .nil t
        (CTm.appSpine (.const k) args) (.const (listAt A).type) :=
  instance_canonical (listAt_admissible typed free) (listAt_avoids A) atType

/-- **Conversion completeness at `List A`.** Derivably equal terms of a formed
context of the package are algorithmically equal. -/
theorem listAt_algorithmicComplete {A : Tm Tower.Head 0}
    (typed : CTyped objectChurch .nil (liftTm A) (.head (.sort Tower.zero)))
    (free : lamFree A = true) :
    AlgorithmicComplete (dataRules (listAt A)) (dataRoles (listAt A)) :=
  instance_algorithmicComplete (listAt_admissible typed free) (listAt_avoids A)

/-- **`nil` and `cons` at `List A`.** No closed equality of the empty list with
`cons a l` is derivable at `List A`. Cite this name for a refutation at the
instance. -/
theorem listAt_nil_ne_cons {A : Tm Tower.Head 0}
    (typed : CTyped objectChurch .nil (liftTm A) (.head (.sort Tower.zero)))
    (free : lamFree A = true) (a l : CTm Tower.Head 0) :
    ¬ CEqual (dataChurch (listAt A)) .nil (.const nilN)
      (.app (.app (.const consN) a) l) (.const listN) :=
  instance_ctor_not_equal (listAt_admissible typed free) (i := 0) (j := 1)
    rfl rfl (by decide) [] [a, l]

/-! ## Two parameters: `Pair A B` -/

/-- The type `Pair`. -/
def pairN : DeclName := .str .anonymous "param-pair"

/-- The constructor of `Pair`. -/
def pairMkN : DeclName := .str .anonymous "param-pair-mk"

/-- The recursor of `Pair`. -/
def pairRecN : DeclName := .str .anonymous "param-pair-rec"

/-- Two parameters, each a type of the least universe. The constructor carries
both, outermost first. -/
def pairParameter : Parameterization Tower.Head where
  telescope := ⟨2, .snoc (.snoc .nil (.head (.sort Tower.zero))) (.head (.sort Tower.zero))⟩
  constructors := [(pairMkN, [.plain (.var 1), .plain (.var 0)])]

/-- `Pair`, with its parameters open. -/
def pairOpen : Datatype Tower.Head where
  type := pairN
  typeUniverse := .sort Tower.zero
  ctors := []
  recursor := pairRecN
  motiveUniverse := listMotives
  parameters := pairParameter

/-- Index `0` is the inner parameter and index `1` is the outer one. -/
def pairSub (A B : Tm Tower.Head 0) : Sub Tower.Head 2 0 :=
  Fin.cases B (fun _ => A)

/-- `Pair A B`. -/
def pairAt (A B : Tm Tower.Head 0) : Datatype Tower.Head :=
  pairOpen.instantiate (pairSub A B)

@[simp] theorem pairAt_ctors (A B : Tm Tower.Head 0) :
    (pairAt A B).ctors = [(pairMkN, [.closed A, .closed B])] := rfl

/-- Substituting the two parameters sends `Pair` at its parameters to
`Pair A B`, outermost first. -/
theorem pairAt_type (A B : Tm Tower.Head 0) :
    Presentation.subst (pairSub A B) (dataInstance pairN 2) =
      .app (.app (.const pairN) A) B := by
  rw [subst_dataInstance]
  simp only [substParams, pairSub, tailSub, Fin.cases_zero, Fin.cases_succ]
  rfl

theorem pairOpen_admissible : ParameterAdmissible objectChurch pairOpen where
  telescope := ⟨⟨trivial, CIsType.head_of_universe (P := objectChurch) (Γ := .nil)
    ConvRules.objectLevels (LevelTower.IsUniverse.sort _)⟩,
    CIsType.head_of_universe (P := objectChurch)
      (Γ := .snoc .nil (liftTm (.head (.sort Tower.zero))))
      ConvRules.objectLevels (LevelTower.IsUniverse.sort _)⟩
  fields := by
    intro k fs member f fm
    dsimp [pairOpen, pairParameter] at member fm
    cases List.mem_singleton.mp member
    cases List.mem_cons.mp fm with
    | inl eq =>
      cases eq
      rfl
    | inr rest =>
      cases List.mem_cons.mp rest with
      | inl eq =>
        cases eq
        rfl
      | inr rest => cases rest
  exclusive := Or.inr rfl

theorem pairAt_mor {A B : Tm Tower.Head 0}
    (typedA : CTyped objectChurch .nil (liftTm A) (.head (.sort Tower.zero)))
    (typedB : CTyped objectChurch .nil (liftTm B) (.head (.sort Tower.zero))) :
    CSubstMor objectChurch (liftCtx pairOpen.parameters.telescope.context) .nil
      (fun i => liftTm (pairSub A B i)) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · exact typedB
  · intro j
    obtain rfl : j = 0 := Subsingleton.elim j 0
    exact typedA

theorem pairAt_plain {k : DeclName} {fs : List (OpenField Tower.Head 2)}
    {ty : Tm Tower.Head 2} (member : (k, fs) ∈ pairOpen.parameters.constructors)
    (fm : .plain ty ∈ fs) :
    CTyped objectChurch (liftCtx pairOpen.parameters.telescope.context) (liftTm ty)
      (.head (.sort Tower.zero)) := by
  dsimp [pairOpen, pairParameter, liftCtx] at member fm ⊢
  cases List.mem_singleton.mp member
  cases List.mem_cons.mp fm with
  | inl eq =>
    injection eq with h
    cases h
    exact .var 1
  | inr rest =>
    cases List.mem_cons.mp rest with
    | inl eq =>
      injection eq with h
      cases h
      exact .var 0
    | inr rest => cases rest

theorem pairAt_avoids (A B : Tm Tower.Head 0) : AvoidsModelNames (pairAt A B) := by
  intro c mem
  simp only [dataNames, pairAt, Datatype.instantiate, pairOpen, pairParameter,
    List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl <;> decide

/-- **`Pair A B` is admissible** when both parameters are types of the least
universe and contain no abstraction. -/
theorem pairAt_admissible {A B : Tm Tower.Head 0}
    (typedA : CTyped objectChurch .nil (liftTm A) (.head (.sort Tower.zero)))
    (typedB : CTyped objectChurch .nil (liftTm B) (.head (.sort Tower.zero)))
    (freeA : lamFree A = true) (freeB : lamFree B = true) :
    (pairAt A B).Admissible objectChurch :=
  Datatype.instantiate_admissible (d := pairOpen) (σ := pairSub A B) pairOpen_admissible
    (LevelTower.IsUniverse.sort _) (LevelTower.IsUniverse.sort _)
    { ctorsNodup := by
        show ([pairMkN] : List DeclName).Nodup
        decide
      typeNotCtor := by
        show pairN ∉ [pairMkN]
        decide
      recNotType := by decide
      recNotCtor := by
        show pairRecN ∉ [pairMkN]
        decide }
    { typeNew := by decide
      recNew := by decide
      ctorsNew := by
        intro entry member
        dsimp [Datatype.instantiate, pairOpen, pairParameter] at member
        cases List.mem_singleton.mp member
        show objectChurch.constantType pairMkN = none
        decide }
    (fun i => by
      dsimp [pairOpen, pairParameter] at i
      refine Fin.cases ?_ ?_ i
      · exact freeB
      · intro j
        obtain rfl : j = 0 := Subsingleton.elim j 0
        exact freeA)
    (pairAt_mor typedA typedB) pairAt_plain

/-! ## A parameter in a negative position: `Pred A` -/

/-- The type `Pred`. -/
def predTypeN : DeclName := .str .anonymous "param-pred"

/-- The constructor of `Pred`. -/
def predMkN : DeclName := .str .anonymous "param-pred-mk"

/-- The recursor of `Pred`. -/
def predRecN : DeclName := .str .anonymous "param-pred-rec"

/-- `Pred`, one parameter, and one constructor of the field `A → num`. -/
def predOpen : Datatype Tower.Head :=
  predData predTypeN predMkN predRecN numN (.sort Tower.zero) (.sort (.succ Tower.zero))

/-- `Pred A`. -/
def predAt (A : Tm Tower.Head 0) : Datatype Tower.Head :=
  predOpen.instantiate (fun _ => A)

@[simp] theorem predAt_ctors (A : Tm Tower.Head 0) :
    (predAt A).ctors = [(predMkN, [.closed (.pi A (.const numN))])] := rfl

theorem predOpen_admissible : ParameterAdmissible objectChurch predOpen :=
  pred_admissible ConvRules.objectLevels predTypeN predMkN predRecN numN
    (.sort Tower.zero) (.sort (.succ Tower.zero)) (LevelTower.IsUniverse.sort _) (by decide)

theorem predAt_mor {A : Tm Tower.Head 0}
    (typed : CTyped objectChurch .nil (liftTm A) (.head (.sort Tower.zero))) :
    CSubstMor objectChurch (liftCtx predOpen.parameters.telescope.context) .nil
      (fun _ => liftTm A) := by
  intro i
  dsimp [predOpen, predData, liftCtx] at i ⊢
  obtain rfl : i = 0 := Subsingleton.elim i 0
  exact typed

/-- The field `A → num` is a type of the least universe in the parameter
context. -/
theorem predAt_plain {k : DeclName} {fs : List (OpenField Tower.Head 1)}
    {ty : Tm Tower.Head 1} (member : (k, fs) ∈ predOpen.parameters.constructors)
    (fm : .plain ty ∈ fs) :
    CTyped objectChurch (liftCtx predOpen.parameters.telescope.context) (liftTm ty)
      (.head (.sort Tower.zero)) := by
  dsimp [predOpen, predData, liftCtx] at member fm ⊢
  cases List.mem_singleton.mp member
  have field : .plain ty = predField (Head := Tower.Head) numN := List.mem_singleton.mp fm
  unfold predField at field
  injection field with eq
  cases eq
  exact cpiT (.var 0) cnum_typed

theorem predAt_avoids (A : Tm Tower.Head 0) : AvoidsModelNames (predAt A) := by
  intro c mem
  simp only [dataNames, predAt, Datatype.instantiate, predOpen, predData, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl <;> decide

/-- **`Pred A` is admissible.** The parameter stands in the domain of the field
`A → num`. -/
theorem predAt_admissible {A : Tm Tower.Head 0}
    (typed : CTyped objectChurch .nil (liftTm A) (.head (.sort Tower.zero)))
    (free : lamFree A = true) : (predAt A).Admissible objectChurch :=
  Datatype.instantiate_admissible (d := predOpen) (σ := fun _ => A) predOpen_admissible
    (LevelTower.IsUniverse.sort _) (LevelTower.IsUniverse.sort _)
    { ctorsNodup := by
        show ([predMkN] : List DeclName).Nodup
        decide
      typeNotCtor := by
        show predTypeN ∉ [predMkN]
        decide
      recNotType := by decide
      recNotCtor := by
        show predRecN ∉ [predMkN]
        decide }
    { typeNew := by decide
      recNew := by decide
      ctorsNew := by
        intro entry member
        dsimp [Datatype.instantiate, predOpen, predData] at member
        cases List.mem_singleton.mp member
        show objectChurch.constantType predMkN = none
        decide }
    (fun i => by
      dsimp [predOpen, predData] at i
      obtain rfl : i = 0 := Subsingleton.elim i 0
      exact free)
    (predAt_mor typed) predAt_plain

/-! ## An instance at a term of the wrong universe -/

/-- **`List zero` is not admissible.** Zero is a number, so it is not a type of
the datatype's universe, and the closed field of `cons` asks it to be one. -/
theorem listAt_zero_not_admissible :
    ¬ (listAt (.const zeroN)).Admissible objectChurch := by
  intro adm
  have mem : (consN, [Presentation.TypedEquality.Normalization.Field.closed (.const zeroN),
      Presentation.TypedEquality.Normalization.Field.recursive]) ∈
      (listAt (.const zeroN)).ctors := by
    rw [listAt_ctors]
    exact List.mem_cons_of_mem (nilN, []) List.mem_cons_self
  have field :
      Presentation.TypedEquality.Normalization.Field.closed (Head := Tower.Head)
        (Tm.const (Head := Tower.Head) zeroN) ∈
      ([Presentation.TypedEquality.Normalization.Field.closed (Head := Tower.Head)
          (Tm.const (Head := Tower.Head) zeroN),
        Presentation.TypedEquality.Normalization.Field.recursive (Head := Tower.Head)] :
        List (Presentation.TypedEquality.Normalization.Field Tower.Head)) :=
    List.mem_cons_self
  have typing := adm.fields _ mem _ field
  have progress := objectChurch_typeProgress .nil (.sort _) typing
  rcases progress with ⟨A', step⟩ | form
  · exact CWhStepR.not_of_whnf (constSpine_whnf objectShape (c := zeroN)
      (fun _ _ h => nomatch objectRoles_zero.symm.trans h) []) A' step
  · rcases form with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ | neutral |
      ⟨_, _, role, e⟩
    · cases e
    · cases e
    · cases e
    · cases e
    · exact neutral.not_canonical (.inr ⟨zeroN, 0, [], objectRoles_zero, rfl⟩)
    · cases e
      rw [objectRoles_zero] at role
      cases role

/-! ## The declaring package -/

/-- Lists of numbers, as a simple datatype. The parameterization is empty. -/
def listsSimple : Datatype Tower.Head where
  type := listN
  typeUniverse := .sort Tower.zero
  ctors := listCtors
  recursor := listRecN
  motiveUniverse := listMotives

/-- **The declaring package of the lists of numbers is their simple package.** -/
theorem listsSimple_rules :
    parameterRules objectRules listsSimple =
      inductiveRules objectRules listN (.sort Tower.zero) listCtors listRecN listMotives :=
  parameterRules_of_none objectRules listsSimple rfl

/-- `nil` of the open lists is declared at `Π (A : U₀). List A`. -/
theorem listOpen_nil_type :
    parameterDecls listOpen nilN =
      some (.pi (.head (.sort Tower.zero)) (.app (.const listN) (.var 0))) := rfl

/-- The nil rule of the open lists. The recursor is applied to the parameter, the
motive and the two methods, and the scrutinee is `nil` at that parameter. -/
theorem listOpen_nil_iota_left :
    openIotaLeft (Head := Tower.Head) listRecN nilN 1 2 0 =
      recApp listRecN
        ([.var 3, .var 2, .var 1, .var 0] : List (Tm Tower.Head 4))
        (.app (.const nilN) (.var 3)) := rfl

/-- `Pair`'s constructor is declared at its type closed over the two parameters. -/
theorem pairOpen_mk_type :
    parameterDecls pairOpen pairMkN =
      some (TelescopeAbstraction.closeType pairParameter.telescope.context
        (ctorOpen pairN 2 [.plain (.var 1), .plain (.var 0)] 0)) := rfl

/-- `Pred`'s constructor is declared at its type closed over the parameter. The
field is `A → num`. -/
theorem predOpen_mk_type :
    parameterDecls predOpen predMkN =
      some (TelescopeAbstraction.closeType predOpen.parameters.telescope.context
        (ctorOpen predTypeN 1 [predField numN] 0)) := rfl

end CodeModel
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
