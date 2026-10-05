import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append.Source

/-!
# Lists and their append, as sets

The source of `Source.lean`, read as sets: what each list expression is, independently of how
it runs and of how it is typed.

**The sets.** A numeral is a finite ordinal: zero is `∅` and the successor of `x` is
`x ∪ {x}` (`NumExpr.toSet`). The set of lists (`listSet`) is the least set closed under the
empty list (`nilSet`) and a natural number before a list (`consSet`): the carrier of the
signature of lists over `ω` (`ZFSetInductive.carrier`, `listSignature`). A constructor is read
by its name: the empty list is the code of the name `nil` paired with the empty tuple, and a
number before a list is the code of the name `cons` paired with the tuple of the two
(`ZFSetInductive.nameCode`, `ZFSetInductive.constructorValue`). Its induction principle
(`list_induct`) is the induction of that carrier.

**The append, on sets alone.** By the recursion of the set of lists
(`ZFSetInductive.recFun`) every list gives a function from lists to lists, coded as a set
(the traced graph over `listSet`): the identity at the empty list, and at `consSet a l` the
function that puts `a` before the value of the function of `l` (`appendFun`). The append of
two sets is the function of the first applied to the second (`setAppend`). It satisfies the
two equations of the source (`setAppend_nil`, `setAppend_cons`), sends two lists to a list
(`setAppend_mem`), is associative (`setAppend_assoc`), and is the only function on lists with
those two equations (`setAppend_unique`). Nothing of the type theory is used to define it.

**The reading of the source** (`ListExpr.toSet`): `nil` is `nilSet`, `cons` is `consSet` and
`append` is `setAppend`; every expression is read as a list (`ListExpr.toSet_mem`). A step of
the source does not change the set (`ListExpr.Step.toSet_eq`), nor does a sequence of steps
(`ListExpr.toSet_eq_of_steps`). Every list appended to the empty list is the list
(`setAppend_nil_right`), by induction on the set of lists.

**What is typed means this set** (`toTerm_value`). In the set model of the program with the
lists, the append and the proof that appending the empty list changes nothing
(`objectProgram_model`, relative to `CofinalInaccessibles`), the value of the term of an
expression is the set of the expression. The model's value of `append` is built from the
typed right sides of its equations; it agrees with `setAppend` on lists because the two typed
equations hold in the model at every list (`model_append_nil`, `model_append_cons`) and
`setAppend` is the only function with them (`model_append`).

Positive example: `one ++ two` is the list of `0` and `1` (`append_one_two_toSet`), and so is
the value of its term in the model (`append_one_two_value`). Negative examples: the lists
`one` and `two` are different sets (`one_ne_two_toSet`); the append is not commutative,
`one ++ two` and `two ++ one` are different sets with different values in the model
(`append_not_commutative`, `append_one_two_value_ne`); and the empty set is not a list
(`empty_not_mem_listSet`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Presentation Presentation.TypedEquality.Annotated
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
open CodeModel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInductive (Fits constructorValue carrier recFun nameCode DistinctTags
  constructor_mem_carrier carrier_induct recFun_constructor constructorValue_injective
  numeral_zero_ne_one)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp traceApp_graph_beta)

universe u

/-! ## The set of lists -/

/-- **The signature of the lists of natural numbers**: the empty list, and a member of `ω`
before a list. The two constructors carry the codes of the names `nil` and `cons`. -/
def listSignature : ZFSetInductive.Signature.{u} :=
  [⟨nameCode nilN, []⟩,
    ⟨nameCode consN, [ZFSetInductive.Field.ofSet ZFSet.omega, ZFSetInductive.Field.recursive]⟩]

/-- The two constructors have different names, so their tags are distinct. -/
theorem listSignature_distinct : DistinctTags listSignature.{u} :=
  ZFSetInductive.distinctTags_pair (ZFSetInductive.nameCode_injective.ne (by decide))

/-- **The set of the lists of natural numbers**: the least set closed under the empty list and
a member of `ω` before a list. -/
noncomputable abbrev listSet : ZFSet.{u} := carrier listSignature

/-- The empty list as a set: the code of the name `nil` at no argument. -/
def nilSet : ZFSet.{u} := constructorValue (nameCode nilN) []

/-- A number before a list, as a set: the code of the name `cons` at the two. -/
def consSet (a l : ZFSet.{u}) : ZFSet.{u} := constructorValue (nameCode consN) [a, l]

/-- The empty list is a list. -/
theorem nilSet_mem : nilSet.{u} ∈ listSet.{u} :=
  constructor_mem_carrier (sig := listSignature) (i := 0) (c := ⟨nameCode nilN, []⟩)
    (args := []) rfl Fits.nil

/-- A natural number before a list is a list. -/
theorem consSet_mem {a l : ZFSet.{u}} (ha : a ∈ ZFSet.omega) (hl : l ∈ listSet) :
    consSet a l ∈ listSet :=
  constructor_mem_carrier (sig := listSignature) (i := 1)
    (c := ⟨nameCode consN,
      [ZFSetInductive.Field.ofSet ZFSet.omega, ZFSetInductive.Field.recursive]⟩)
    (args := [a, l]) rfl (Fits.ofSet ha (Fits.recursive hl Fits.nil))

/-- **Induction on the set of lists**: a property of the empty list that passes from a list to
a natural number before it holds of every list. It is the induction of the carrier. -/
theorem list_induct {P : ZFSet.{u} → Prop} (nil : P nilSet)
    (cons : ∀ a l, a ∈ ZFSet.omega → l ∈ listSet → P l → P (consSet a l)) :
    ∀ l, l ∈ listSet → P l := by
  intro l member
  refine (carrier_induct (sig := listSignature)
    (P := fun y => y ∈ listSet ∧ P y) ?_ member).2
  intro i c args atIndex fitting
  have bound := ZFSetInductive.some_index_lt atIndex
  cases i with
  | zero =>
      have hc : c = ⟨nameCode nilN, []⟩ := (Option.some_inj).mp atIndex.symm
      subst hc
      cases (fitting : ZFSetInductive.FitsPred _ [] args)
      exact ⟨nilSet_mem, nil⟩
  | succ i =>
      cases i with
      | zero =>
          have hc : c = ⟨nameCode consN,
              [ZFSetInductive.Field.ofSet ZFSet.omega, ZFSetInductive.Field.recursive]⟩ :=
            (Option.some_inj).mp atIndex.symm
          subst hc
          cases (fitting : ZFSetInductive.FitsPred _
            [ZFSetInductive.Field.ofSet ZFSet.omega, ZFSetInductive.Field.recursive] args) with
          | ofSet headMember tailFit =>
              cases tailFit with
              | recursive tail rest =>
                  cases rest
                  exact ⟨consSet_mem headMember tail.1, cons _ _ headMember tail.1 tail.2⟩
      | succ i => exact (Nat.not_lt.mpr (Nat.le_add_left 2 i) bound).elim

/-- Negative example: the empty set is not a list. Every list is a tagged pair. -/
theorem empty_not_mem_listSet : (∅ : ZFSet.{u}) ∉ listSet.{u} := by
  intro member
  obtain ⟨_, c, args, _, _, value⟩ := ZFSetInductive.exists_inversion member
  exact ZFSetInductive.constructorValue_ne_empty c.tag args value

/-! ## The append, by the recursion of the set of lists -/

/-- **What the recursion of the append does at a constructor.** A function on lists is coded
as the traced graph of its values over `listSet`. At the empty list the result is the
identity; at a number `a` before a list, whose function is `r`, the result puts `a` before
the value of `r`. -/
noncomputable def appendCase (i : Nat) (args recs : List ZFSet.{u}) : ZFSet.{u} :=
  if i = 0 then traceLam (graph listSet fun ys => ys)
  else
    match args, recs with
    | a :: _, r :: _ => traceLam (graph listSet fun ys => consSet a (traceApp r ys))
    | _, _ => ∅

/-- **The function of a list**, by the recursion of the set of lists. -/
noncomputable def appendFun : ZFSet.{u} → ZFSet.{u} :=
  recFun (sig := listSignature) appendCase

/-- **The append of two sets**: the function of the first, applied to the second. -/
noncomputable def setAppend (l ys : ZFSet.{u}) : ZFSet.{u} := traceApp (appendFun l) ys

/-- The function of the empty list is the identity on lists. -/
theorem appendFun_nil : appendFun nilSet.{u} = traceLam (graph listSet fun ys => ys) :=
  recFun_constructor (sig := listSignature) listSignature_distinct appendCase (i := 0)
    (c := ⟨nameCode nilN, []⟩) (args := []) rfl Fits.nil

/-- The function of a number before a list puts the number before the values of the function
of the list. -/
theorem appendFun_cons {a l : ZFSet.{u}} (ha : a ∈ ZFSet.omega) (hl : l ∈ listSet) :
    appendFun (consSet a l) =
      traceLam (graph listSet fun ys => consSet a (traceApp (appendFun l) ys)) :=
  recFun_constructor (sig := listSignature) listSignature_distinct appendCase (i := 1)
    (c := ⟨nameCode consN,
      [ZFSetInductive.Field.ofSet ZFSet.omega, ZFSetInductive.Field.recursive]⟩)
    (args := [a, l]) rfl (Fits.ofSet ha (Fits.recursive hl Fits.nil))

/-- **The first equation, between sets**: the empty list appended to a list is the list. -/
theorem setAppend_nil {ys : ZFSet.{u}} (hys : ys ∈ listSet) : setAppend nilSet ys = ys := by
  rw [setAppend, appendFun_nil, traceApp_graph_beta _ hys]

/-- **The second equation, between sets**: a number before a list, appended to a list, is the
number before the append of the two lists. -/
theorem setAppend_cons {a l ys : ZFSet.{u}} (ha : a ∈ ZFSet.omega) (hl : l ∈ listSet)
    (hys : ys ∈ listSet) : setAppend (consSet a l) ys = consSet a (setAppend l ys) := by
  rw [setAppend, appendFun_cons ha hl, traceApp_graph_beta _ hys]
  rfl

/-- **Closure**: the append of two lists is a list. -/
theorem setAppend_mem : ∀ l, l ∈ listSet.{u} → ∀ ys, ys ∈ listSet.{u} →
    setAppend l ys ∈ listSet.{u} :=
  list_induct (P := fun l => ∀ ys, ys ∈ listSet → setAppend l ys ∈ listSet)
    (fun ys hys => by
      rw [setAppend_nil hys]
      exact hys)
    (fun a l ha hl ih ys hys => by
      rw [setAppend_cons ha hl hys]
      exact consSet_mem ha (ih ys hys))

/-- **The append is the only function on lists with the two equations**: a function of two
sets that satisfies them agrees with `setAppend` at every two lists. -/
theorem setAppend_unique (g : ZFSet.{u} → ZFSet.{u} → ZFSet.{u})
    (nil : ∀ ys, ys ∈ listSet → g nilSet ys = ys)
    (cons : ∀ a l ys, a ∈ ZFSet.omega → l ∈ listSet → ys ∈ listSet →
      g (consSet a l) ys = consSet a (g l ys)) :
    ∀ l, l ∈ listSet → ∀ ys, ys ∈ listSet → g l ys = setAppend l ys :=
  list_induct (P := fun l => ∀ ys, ys ∈ listSet → g l ys = setAppend l ys)
    (fun ys hys => by rw [nil ys hys, setAppend_nil hys])
    (fun a l ha hl ih ys hys => by
      rw [cons a l ys ha hl hys, setAppend_cons ha hl hys, ih ys hys])

/-- **The theorem of the specimen, between sets**: every list appended to the empty list is
the list. By induction on the set of lists. -/
theorem setAppend_nil_right : ∀ l, l ∈ listSet.{u} → setAppend l nilSet = l :=
  list_induct (P := fun l => setAppend l nilSet = l) (setAppend_nil nilSet_mem)
    (fun a l ha hl ih => by rw [setAppend_cons ha hl nilSet_mem, ih])

/-- **The append on sets is associative**, by induction on the set of lists. -/
theorem setAppend_assoc : ∀ x, x ∈ listSet.{u} → ∀ y, y ∈ listSet.{u} → ∀ z, z ∈ listSet.{u} →
    setAppend (setAppend x y) z = setAppend x (setAppend y z) :=
  list_induct (P := fun x => ∀ y, y ∈ listSet → ∀ z, z ∈ listSet →
      setAppend (setAppend x y) z = setAppend x (setAppend y z))
    (fun y hy z hz => by rw [setAppend_nil hy, setAppend_nil (setAppend_mem _ hy _ hz)])
    (fun a x ha hx ih y hy z hz => by
      rw [setAppend_cons ha hx hy, setAppend_cons ha (setAppend_mem _ hx _ hy) hz, ih y hy z hz,
        setAppend_cons ha hx (setAppend_mem _ hy _ hz)])

/-! ## The source, read as sets -/

/-- **The set of a numeral**: zero is `∅`, and the successor of `x` is `x ∪ {x}`. -/
def NumExpr.toSet : NumExpr → ZFSet.{u}
  | .zero => ∅
  | .suc n => insert n.toSet n.toSet

/-- A numeral is read as a natural number, a member of `ω`. -/
theorem NumExpr.toSet_mem : ∀ n : NumExpr, (n.toSet : ZFSet.{u}) ∈ ZFSet.omega
  | .zero => ZFSet.omega_zero
  | .suc n => ZFSet.omega_succ n.toSet_mem

/-- **The set of a list expression**: the empty list, a number before a list, and the append
of the two sets. -/
noncomputable def ListExpr.toSet : ListExpr → ZFSet.{u}
  | .nil => nilSet
  | .cons head tail => consSet head.toSet tail.toSet
  | .append left right => setAppend left.toSet right.toSet

/-- Every list expression is read as a list. -/
theorem ListExpr.toSet_mem : ∀ e : ListExpr, (e.toSet : ZFSet.{u}) ∈ listSet
  | .nil => nilSet_mem
  | .cons head tail => consSet_mem head.toSet_mem tail.toSet_mem
  | .append left right => setAppend_mem _ left.toSet_mem _ right.toSet_mem

/-- **The two equations hold between sets**: a step of the source does not change the set. -/
theorem ListExpr.Step.toSet_eq {e e' : ListExpr} (step : ListExpr.Step e e') :
    (e.toSet : ZFSet.{u}) = e'.toSet := by
  induction step with
  | appendNil right => exact setAppend_nil right.toSet_mem
  | appendCons head tail right =>
      exact setAppend_cons head.toSet_mem tail.toSet_mem right.toSet_mem
  | consTail _ ih =>
      show consSet _ _ = consSet _ _
      rw [ih]
  | appendLeft _ ih =>
      show setAppend _ _ = setAppend _ _
      rw [ih]
  | appendRight _ ih =>
      show setAppend _ _ = setAppend _ _
      rw [ih]

/-- A sequence of steps does not change the set. -/
theorem ListExpr.toSet_eq_of_steps {e e' : ListExpr}
    (steps : Relation.ReflTransGen ListExpr.Step e e') : (e.toSet : ZFSet.{u}) = e'.toSet := by
  induction steps with
  | refl => rfl
  | tail _ step ih => exact ih.trans step.toSet_eq

/-- Positive example: **`one ++ two` is the list of `0` and `1`.** -/
theorem append_one_two_toSet :
    ((ListExpr.append one two).toSet : ZFSet.{u}) =
      consSet (numeral 0) (consSet (numeral 1) nilSet) :=
  (setAppend_cons (NumExpr.toSet_mem .zero) nilSet_mem (ListExpr.toSet_mem two)).trans
    (congrArg (consSet _) (setAppend_nil (ListExpr.toSet_mem two)))

/-- `two ++ one` is the list of `1` and `0`. -/
theorem append_two_one_toSet :
    ((ListExpr.append two one).toSet : ZFSet.{u}) =
      consSet (numeral 1) (consSet (numeral 0) nilSet) :=
  (setAppend_cons (NumExpr.toSet_mem (.suc .zero)) nilSet_mem (ListExpr.toSet_mem one)).trans
    (congrArg (consSet _) (setAppend_nil (ListExpr.toSet_mem one)))

/-- Two lists with different first numbers are different sets. -/
theorem consSet_ne_of_head_ne {a b l m : ZFSet.{u}} (distinct : a ≠ b) :
    consSet a l ≠ consSet b m := by
  intro same
  have args := (constructorValue_injective.mp same).2
  exact distinct (List.cons.inj args).1

/-- Negative example: **the lists `one` and `two` are different sets**. -/
theorem one_ne_two_toSet : (one.toSet : ZFSet.{u}) ≠ two.toSet :=
  consSet_ne_of_head_ne numeral_zero_ne_one

/-- Negative example: **the append is not commutative**. `one ++ two` and `two ++ one` are
different sets. -/
theorem append_not_commutative :
    ((ListExpr.append one two).toSet : ZFSet.{u}) ≠ (ListExpr.append two one).toSet := by
  rw [append_one_two_toSet, append_two_one_toSet]
  exact consSet_ne_of_head_ne numeral_zero_ne_one

/-! ## What is typed means this set -/

section Model

variable (h : CofinalInaccessibles.{u})

/-- The constants of the object package keep their values in the model of the program. -/
theorem programConsts_object {c : DeclName} (notProof : c ≠ appendNilN)
    (notAppend : c ≠ appendN) (notType : c ≠ listN) (notCtor : c ∉ listCtors.map (·.1))
    (notRec : c ≠ listRecN) :
    objectDeclarationsConsts h listProgram c = objectSetConsts h c := by
  show Function.update (Function.update
      (inductiveConsts (objHeads h) (objectSetConsts h) listN listMotives listCtors listRecN)
      appendN _) appendNilN _ c = _
  rw [Function.update_of_ne notProof, Function.update_of_ne notAppend]
  exact inductiveConsts_agrees (objHeads h) (objectSetConsts h) listN listMotives listCtors
    listRecN c notType notCtor notRec

/-- In the model of the program the numbers are `ω`. -/
theorem program_num : objectDeclarationsConsts h listProgram numN = ZFSet.omega :=
  (programConsts_object h (c := numN) (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans (setConst_num h)

/-- In the model of the program zero is `∅`. -/
theorem program_zero : objectDeclarationsConsts h listProgram zeroN = numeral 0 :=
  (programConsts_object h (c := zeroN) (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans (setConst_zero h)

/-- In the model of the program the successor is the object package's. -/
theorem program_suc : objectDeclarationsConsts h listProgram sucN = objectSetConsts h sucN :=
  programConsts_object h (c := sucN) (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- The model of the program reads the declaration of the lists. -/
theorem program_reading :
    InductiveReading (objHeads h) (objectDeclarationsConsts h listProgram) listN listMotives
      listCtors listRecN :=
  declarations_reading (heads := objHeads h) (base := objectSetConsts h) objectChurch
    listProgram listProgram_admissible listDecl
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (objectDeclarationsConsts h listProgram) fun _ _ => rfl

/-- **The type of lists means the set of lists.** -/
theorem program_list : objectDeclarationsConsts h listProgram listN = listSet := by
  rw [(program_reading h).type]
  show carrier [⟨nameCode nilN, []⟩, ⟨nameCode consN,
    [ZFSetInductive.Field.ofSet (objectDeclarationsConsts h listProgram numN),
      ZFSetInductive.Field.recursive]⟩] = carrier listSignature
  rw [program_num h]
  rfl

/-- The constant `nil` means the empty list. -/
theorem program_nil : objectDeclarationsConsts h listProgram nilN = nilSet :=
  ctor_apply ((program_reading h).ctor (i := 0) rfl) (args := [])
    ((fits_iff _ _ _ _).mpr ⟨rfl, fun j below => absurd below (Nat.not_lt_zero j)⟩)

/-- The constant `cons` applied to a natural number and a list means the number before the
list. -/
theorem program_cons {a l : ZFSet.{u}} (ha : a ∈ ZFSet.omega) (hl : l ∈ listSet) :
    traceApp (traceApp (objectDeclarationsConsts h listProgram consN) a) l = consSet a l :=
  ctor_apply ((program_reading h).ctor (i := 1) rfl) (args := [a, l])
    ((fits_iff _ _ _ _).mpr ⟨rfl, fun j below => by
      match j, below with
      | 0, _ =>
          show a ∈ objectDeclarationsConsts h listProgram numN
          rw [program_num h]
          exact ha
      | 1, _ =>
          show l ∈ objectDeclarationsConsts h listProgram listN
          rw [program_list h]
          exact hl⟩)

/-- **The term of a numeral means its set.** -/
theorem num_value : ∀ n : NumExpr,
    ev (objHeads h) (objectDeclarationsConsts h listProgram) n.toTerm Fin.elim0 = n.toSet
  | .zero => program_zero h
  | .suc n => by
      show traceApp (objectDeclarationsConsts h listProgram sucN)
          (ev (objHeads h) (objectDeclarationsConsts h listProgram) n.toTerm Fin.elim0) =
        insert n.toSet n.toSet
      rw [num_value n, program_suc h, suc_apply h n.toSet_mem]

/-- **The first typed equation of the append holds in the model at every list**: the model's
`append` at the empty list returns its second argument. -/
theorem model_append_nil {ys : ZFSet.{u}} (hys : ys ∈ listSet) :
    traceApp (traceApp (objectDeclarationsConsts h listProgram appendN) nilSet) ys = ys := by
  have holds := objectDeclarations_sound h listProgram_admissible
    (ofAppend (append_nil_rule (Γ := .snoc .nil clist) (.var 0)))
  have sat : Sat (objHeads h) (objectDeclarationsConsts h listProgram)
      (.snoc .nil clist) (extend Fin.elim0 ys) := by
    refine (sat_snoc (objHeads h) (objectDeclarationsConsts h listProgram)).mpr
      ⟨sat_nil _ _ _, ?_⟩
    show ys ∈ objectDeclarationsConsts h listProgram listN
    rw [program_list h]
    exact hys
  have equal : traceApp (traceApp (objectDeclarationsConsts h listProgram appendN)
      (objectDeclarationsConsts h listProgram nilN)) ys = ys := (holds _ sat).1
  rwa [program_nil h] at equal

/-- **The second typed equation of the append holds in the model at every number and two
lists.** -/
theorem model_append_cons {a l ys : ZFSet.{u}} (ha : a ∈ ZFSet.omega) (hl : l ∈ listSet)
    (hys : ys ∈ listSet) :
    traceApp (traceApp (objectDeclarationsConsts h listProgram appendN) (consSet a l)) ys =
      consSet a (traceApp (traceApp (objectDeclarationsConsts h listProgram appendN) l) ys) := by
  have equation := objectDeclarations_sound h listProgram_admissible
    (ofAppend (append_cons_rule (Γ := .snoc (.snoc (.snoc .nil cnum) clist) clist)
      (.var 2) (.var 1) (.var 0)))
  have typing := objectDeclarations_sound h listProgram_admissible
    (ofAppend (cappend_typed (Γ := .snoc (.snoc (.snoc .nil cnum) clist) clist)
      (.var 1) (.var 0)))
  let ρ : Env.{u} 3 := extend (extend (extend Fin.elim0 a) l) ys
  have sat : Sat (objHeads h) (objectDeclarationsConsts h listProgram)
      (.snoc (.snoc (.snoc .nil cnum) clist) clist) ρ := by
    refine (sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr
      ⟨sat_nil _ _ _, ?_⟩, ?_⟩, ?_⟩
    · show a ∈ objectDeclarationsConsts h listProgram numN
      rw [program_num h]
      exact ha
    · show l ∈ objectDeclarationsConsts h listProgram listN
      rw [program_list h]
      exact hl
    · show ys ∈ objectDeclarationsConsts h listProgram listN
      rw [program_list h]
      exact hys
  have equal : traceApp (traceApp (objectDeclarationsConsts h listProgram appendN)
        (traceApp (traceApp (objectDeclarationsConsts h listProgram consN) a) l)) ys =
      traceApp (traceApp (objectDeclarationsConsts h listProgram consN) a)
        (traceApp (traceApp (objectDeclarationsConsts h listProgram appendN) l) ys) :=
    (equation ρ sat).1
  have member : traceApp (traceApp (objectDeclarationsConsts h listProgram appendN) l) ys ∈
      listSet := by
    have inList : traceApp (traceApp (objectDeclarationsConsts h listProgram appendN) l) ys ∈
        objectDeclarationsConsts h listProgram listN := typing ρ sat
    rwa [program_list h] at inList
  rwa [program_cons h ha hl, program_cons h ha member] at equal

/-- **The model's append is the append on sets** at every two lists: it has the two equations,
and `setAppend` is the only function on lists that has them. -/
theorem model_append {l ys : ZFSet.{u}} (hl : l ∈ listSet) (hys : ys ∈ listSet) :
    traceApp (traceApp (objectDeclarationsConsts h listProgram appendN) l) ys =
      setAppend l ys :=
  setAppend_unique
    (fun l ys => traceApp (traceApp (objectDeclarationsConsts h listProgram appendN) l) ys)
    (fun _ hys => model_append_nil h hys)
    (fun _ _ _ ha hl hys => model_append_cons h ha hl hys) l hl ys hys

/-- **What is typed means this set**: in the set model of the program, the value of the term
of a list expression is the set of the expression. -/
theorem toTerm_value : ∀ e : ListExpr,
    ev (objHeads h) (objectDeclarationsConsts h listProgram) e.toTerm Fin.elim0 = e.toSet
  | .nil => program_nil h
  | .cons head tail => by
      show traceApp (traceApp (objectDeclarationsConsts h listProgram consN)
          (ev (objHeads h) (objectDeclarationsConsts h listProgram) head.toTerm Fin.elim0))
          (ev (objHeads h) (objectDeclarationsConsts h listProgram) tail.toTerm Fin.elim0) =
        consSet head.toSet tail.toSet
      rw [num_value h head, toTerm_value tail]
      exact program_cons h head.toSet_mem tail.toSet_mem
  | .append left right => by
      show traceApp (traceApp (objectDeclarationsConsts h listProgram appendN)
          (ev (objHeads h) (objectDeclarationsConsts h listProgram) left.toTerm Fin.elim0))
          (ev (objHeads h) (objectDeclarationsConsts h listProgram) right.toTerm Fin.elim0) =
        setAppend left.toSet right.toSet
      rw [toTerm_value left, toTerm_value right]
      exact model_append h left.toSet_mem right.toSet_mem

/-- A step of the source does not change the value of the term in the model. -/
theorem step_value {e e' : ListExpr} (step : ListExpr.Step e e') :
    ev (objHeads h) (objectDeclarationsConsts h listProgram) e.toTerm Fin.elim0 =
      ev (objHeads h) (objectDeclarationsConsts h listProgram) e'.toTerm Fin.elim0 := by
  rw [toTerm_value h, toTerm_value h]
  exact step.toSet_eq

/-- Positive example: the value of the term of `one ++ two` in the model is the list of `0`
and `1`. -/
theorem append_one_two_value :
    ev (objHeads h) (objectDeclarationsConsts h listProgram) (ListExpr.append one two).toTerm
        Fin.elim0 =
      consSet (numeral 0) (consSet (numeral 1) nilSet) :=
  (toTerm_value h _).trans append_one_two_toSet

/-- Negative example: the terms of `one ++ two` and `two ++ one` have different values in the
model. -/
theorem append_one_two_value_ne :
    ev (objHeads h) (objectDeclarationsConsts h listProgram) (ListExpr.append one two).toTerm
        Fin.elim0 ≠
      ev (objHeads h) (objectDeclarationsConsts h listProgram) (ListExpr.append two one).toTerm
        Fin.elim0 := by
  rw [toTerm_value h, toTerm_value h]
  exact append_not_commutative

end Model

end Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append
