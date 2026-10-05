import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.InductivePackage

/-!
# What the left side of a recursor's computation rule knows

`iotaLeft` is the recursor applied to the motive, one method for each constructor,
and the constructor applied to its fields. Each of those metavariables occurs once.
Its knowledge at that metavariable is the corresponding entry of `iotaTele`.

**The rules of a declared datatype in a package that contains its declaration**
(`ChurchRulesSub`, and `StepsWithin` for its computation steps with their premises). Programs
use several datatypes and definitions together, and a recursor of one datatype is applied at
motives and methods that mention the others. In every containing package:

* a constructor applied to terms of the types of its fields is a term of the declared type
  (`ctor_spine_typed_within`);
* the recursor applied along a substitution typed along its telescope has the motive's type
  at the scrutinee (`rec_applied_within`);
* **the computation rule of the recursor, with the typings of its arguments as its only
  premises** (`iota_holds_within`): an instance at a substitution typed along the telescope of
  the rule's metavariables is an equality at the motive at the constructor applied to its
  fields. Both sides are typed by `iota_typed_metaVars`, and the knowledge of the rule's left
  side is the telescope of its metavariables (`iotaLeft_known`);
* **the computation rules preserve typing and are premised** (`iota_preservesIn`,
  `iota_premisedIn`), given the injectivity and no-confusion of the containing package's type
  formers: pattern inversion types the motive, the methods and the fields of a typed redex
  along the rule's telescope, and the left side synthesizes the motive at the constructor
  applied to its fields (`iotaLeft_type`). A template typed in a package is typed in every
  package containing it (`TemplateTyped.mono`).

The arguments are typed in the containing package, so they may use constants that the
declaration's own package does not have. `iota_holds` is the case of the declaration's own
package.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Normalization (Field)
open TelescopeAbstraction (closeType)

variable {Head : Type}

/-! ## Index arithmetic -/

theorem index_lt (n q : Nat) (hq : q < n) : n - 1 - q < n :=
  Nat.lt_of_le_of_lt (Nat.sub_le (n - 1) q) (Nat.pred_lt (Nat.ne_of_gt (Nat.zero_lt_of_lt hq)))

theorem index_back (n jv : Nat) (hj : jv < n) : n - 1 - (n - 1 - jv) = jv :=
  Nat.sub_sub_self (Nat.le_sub_of_add_le (Nat.succ_le_of_lt hj))

theorem sub_left_inj {a b c : Nat} (hb : b ≤ a) (hc : c ≤ a) (h : a - b = a - c) : b = c := by
  have hb' : a - (a - b) = b := Nat.sub_sub_self hb
  rw [h] at hb'
  exact hb'.symm.trans (Nat.sub_sub_self hc)

theorem sub_sub_cancel_add (a b c : Nat) (hc : c ≤ b) (hb : b ≤ a) :
    a - (b - c) = a - b + c := by
  have hle : c ≤ a - (b - c) := by
    apply Nat.le_sub_of_add_le
    rw [Nat.add_comm, Nat.sub_add_cancel hc]
    exact hb
  rw [← Nat.sub_add_cancel hle, Nat.sub_sub, Nat.sub_add_cancel hc]

theorem sub_one_add (n q : Nat) (hq : q < n) : n - 1 - q + 1 = n - q := by
  have h1 : 1 ≤ n - q := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hq)
  rw [Nat.sub_sub, Nat.add_comm 1 q, ← Nat.sub_sub, Nat.sub_add_cancel h1]

theorem sub_succ_eq (n q : Nat) (hq : q ≤ n) : n + 1 - q = n - q + 1 := by
  refine (Nat.sub_eq_iff_eq_add' (Nat.le_trans hq (Nat.le_succ n))).mpr ?_
  show n + 1 = q + ((n - q) + 1)
  rw [← Nat.add_assoc, Nat.add_comm q (n - q), Nat.sub_add_cancel hq]

theorem index_shift (n q s : Nat) (hs : s < q) (hq : q ≤ n) :
    n - 1 - (q - 1 - s) = s + (n - q) := by
  have hq1 : 1 ≤ q := Nat.succ_le_of_lt (Nat.zero_lt_of_lt hs)
  have hsle : s ≤ q - 1 := Nat.le_sub_of_add_le (Nat.succ_le_of_lt hs)
  have hqle : q - 1 ≤ n - 1 := Nat.sub_le_sub_right hq 1
  have hshift : n - (q - 1) = n - q + 1 := by
    refine (Nat.sub_eq_iff_eq_add' (Nat.le_trans (Nat.sub_le q 1) hq)).mpr ?_
    show n = (q - 1) + ((n - q) + 1)
    rw [Nat.add_comm (n - q) 1, ← Nat.add_assoc, Nat.sub_add_cancel hq1, Nat.add_comm,
      Nat.sub_add_cancel hq]
  have hpred : n - 1 - (q - 1) = n - q := by
    rw [Nat.sub_right_comm, hshift, Nat.add_sub_cancel]
  rw [sub_sub_cancel_add (n - 1) (q - 1) s hsle hqle, hpred, Nat.add_comm]

theorem one_add_add_one (c : Nat) : (1 + c) + 1 = c + 2 := by
  rw [Nat.add_comm 1 c, Nat.add_assoc]

theorem cancel_one_add (c a : Nat) : (1 + c + a) - 1 = c + a := by
  rw [Nat.add_comm 1 c, Nat.add_assoc, Nat.add_comm 1 a, ← Nat.add_assoc, Nat.add_sub_cancel]

theorem high_position_le (c a jv : Nat) (hj : a ≤ jv) : (1 + c + a) - 1 - jv ≤ c := by
  have hanti : (1 + c + a) - 1 - jv ≤ (1 + c + a) - 1 - a :=
    Nat.sub_le_sub_left hj ((1 + c + a) - 1)
  have hbase : (1 + c + a) - 1 - a = c := by
    rw [Nat.sub_right_comm, Nat.add_sub_cancel, Nat.add_sub_cancel_left]
  exact Nat.le_trans hanti (Nat.le_of_eq hbase)

theorem prefix_val_ge (c a r : Nat) (hr : r < 1 + c) : a ≤ (1 + c + a) - 1 - r := by
  have hrle : r ≤ c := by
    rw [Nat.add_comm] at hr
    exact Nat.le_of_lt_add_one hr
  have hanti : (1 + c + a) - 1 - c ≤ (1 + c + a) - 1 - r :=
    Nat.sub_le_sub_left hrle ((1 + c + a) - 1)
  have hdrop : (1 + c + a) - c = 1 + a := by
    rw [Nat.add_assoc, Nat.add_comm c a, ← Nat.add_assoc, Nat.add_sub_cancel]
  have hbase : (1 + c + a) - 1 - c = a := by
    rw [Nat.sub_right_comm, hdrop, Nat.add_sub_cancel_left]
  exact Nat.le_trans (Nat.le_of_eq hbase.symm) hanti

theorem field_var_val (c a p : Nat) (_hp : p < a) :
    (1 + c + a) - 1 - (1 + c + p) = a - 1 - p := by
  have hsum : (1 + c) + p + (a - p) = (1 + c) + a := by
    rw [Nat.add_assoc, Nat.add_sub_of_le (Nat.le_of_lt _hp)]
  have hdiff : (1 + c) + a - ((1 + c) + p) = a - p := by
    rw [← hsum, Nat.add_sub_cancel_left]
  rw [Nat.sub_right_comm (1 + c + a) 1 (1 + c + p), hdiff]
  exact Nat.sub_right_comm a p 1

theorem field_position (c a jv : Nat) (hj : jv < a) :
    (1 + c + a) - 1 - jv = c + 1 + (a - 1 - jv) := by
  have hrest : 1 + (a - 1 - jv) = a - jv := by
    rw [Nat.add_comm]
    exact sub_one_add a jv hj
  rw [cancel_one_add, Nat.add_assoc, hrest]
  exact Nat.add_sub_assoc (Nat.le_of_lt hj) c

theorem small_lt (a r : Nat) (hr : r < a) : a - 1 - r < a :=
  Nat.lt_of_le_of_lt (Nat.sub_le (a - 1) r) (Nat.pred_lt (Nat.ne_of_gt (Nat.zero_lt_of_lt hr)))

/-! ## The shift that places an entry in a longer telescope -/

theorem shift_lt {q n : Nat} (h : q ≤ n) (i : Fin q) : i.val + (n - q) < n := by
  have hlt : i.val + (n - q) < q + (n - q) := Nat.add_lt_add_right i.isLt (n - q)
  rw [Nat.add_sub_of_le h] at hlt
  exact hlt

/-- The renaming that adds `n - q` to each variable of a context of length `q`. -/
def shiftBy {q n : Nat} (h : q ≤ n) : Ren q n :=
  fun i => ⟨i.val + (n - q), shift_lt h i⟩

/-- The de Bruijn index of argument position `q` in a context of length `n`. -/
def metaIdx (n q : Nat) (hq : q < n) : Fin n :=
  ⟨n - 1 - q, index_lt n q hq⟩

theorem metaIdx_back {n : Nat} (j : Fin n) :
    metaIdx n (n - 1 - j.val) (index_lt n j.val j.isLt) = j := by
  apply Fin.ext
  exact index_back n j.val j.isLt

theorem metaIdx_inj {n q₁ q₂ : Nat} (h₁ : q₁ < n) (h₂ : q₂ < n)
    (h : metaIdx n q₁ h₁ = metaIdx n q₂ h₂) : q₁ = q₂ := by
  have hv := congrArg Fin.val h
  exact sub_left_inj (Nat.le_sub_of_add_le (Nat.succ_le_of_lt h₁))
    (Nat.le_sub_of_add_le (Nat.succ_le_of_lt h₂)) hv

/-- The de Bruijn index of field `p` among `a` fields, in the rule's context. -/
def fieldIdx (c a p : Nat) (hp : p < a) : Fin (1 + c + a) :=
  ⟨a - 1 - p, Nat.lt_of_le_of_lt (Nat.sub_le (a - 1) p)
      (Nat.lt_of_lt_of_le (Nat.pred_lt (Nat.ne_of_gt (Nat.zero_lt_of_lt hp)))
        (Nat.le_add_left a (1 + c)))⟩

theorem lookup_snoc_zero {n : Nat} (Γ : Ctx Head n) (A : Tm Head n) :
    Ctx.lookup (Ctx.snoc Γ A) 0 = Presentation.rename wk A := rfl

theorem lookup_snoc_succ {n : Nat} (Γ : Ctx Head n) (A : Tm Head n) (i : Fin n) :
    Ctx.lookup (Ctx.snoc Γ A) i.succ = Presentation.rename wk (Ctx.lookup Γ i) := rfl

/-- The entry at position `q` of a telescope sits at de Bruijn index `n - 1 - q`,
renamed by the shift that adds the entries bound after it. -/
theorem telescope_lookup (entry : (j : Nat) → Tm Head j) :
    ∀ (n q : Nat) (hq : q < n),
      Ctx.lookup (Normalization.ofEntries entry n) (metaIdx n q hq) =
        Presentation.rename (shiftBy (Nat.le_of_lt hq)) (entry q)
  | 0, _, hq => absurd hq ((Nat.not_lt).mpr (Nat.zero_le _))
  | n + 1, q, hq => by
      have hsnoc : Normalization.ofEntries entry (n + 1) =
          Ctx.snoc (Normalization.ofEntries entry n) (entry n) := rfl
      rw [hsnoc]
      cases hdec : decide (q = n) with
      | true =>
          have hqEq : n = q := (of_decide_eq_true hdec).symm
          subst hqEq
          have hzero : (n + 1) - 1 - n = 0 := by
            rw [Nat.add_sub_cancel, Nat.sub_self]
          have hfin : metaIdx (n + 1) n hq = 0 := Fin.ext hzero
          rw [hfin, lookup_snoc_zero]
          apply Presentation.rename_ext
          intro i
          apply Fin.ext
          unfold wk shiftBy
          change (i.val + 1) = i.val + ((n + 1) - n)
          rw [Nat.add_sub_cancel_left]
      | false =>
          have hqne : q ≠ n := of_decide_eq_false hdec
          have hqle : q ≤ n := Nat.le_of_lt_add_one hq
          have hq' : q < n := Nat.lt_of_le_of_ne hqle hqne
          have hval : (n + 1) - 1 - q = (n - 1 - q) + 1 := by
            rw [Nat.add_sub_cancel]
            exact (sub_one_add n q hq').symm
          have hfin : metaIdx (n + 1) q hq = Fin.succ (metaIdx n q hq') := Fin.ext hval
          rw [hfin, lookup_snoc_succ, telescope_lookup entry n q hq', Presentation.rename_comp]
          apply Presentation.rename_ext
          intro i
          apply Fin.ext
          show i.val + (n - q) + 1 = i.val + ((n + 1) - q)
          rw [sub_succ_eq n q (Nat.le_of_lt hq'), Nat.add_assoc]

theorem rename_from_closed {n : Nat} (ρ : Ren 0 n) (t : Tm Head 0) :
    Presentation.rename ρ t = Presentation.liftClosed t := by
  have h : ∀ i, ρ i = Fin.elim0 i := fun i => Fin.elim0 i
  rw [Presentation.rename_ext h t]
  rfl

/-- Substituting variables for variables is renaming. -/
theorem subst_varRen {n m : Nat} (ρ : Ren n m) (t : CTm Head n) :
    CTm.subst (fun i => .var (ρ i)) t = CTm.rename ρ t := by
  induction t generalizing m with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB =>
      simp only [CTm.subst, CTm.rename, ihA]
      rw [← ihB (liftRen ρ)]
      apply congrArg (fun body => (CTm.rename ρ A).pi body)
      apply CTm.subst_ext
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · rfl
  | sigma A B ihA ihB =>
      simp only [CTm.subst, CTm.rename, ihA]
      rw [← ihB (liftRen ρ)]
      apply congrArg (fun body => (CTm.rename ρ A).sigma body)
      apply CTm.subst_ext
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · rfl
  | id A a b ihA iha ihb =>
      simp only [CTm.subst, CTm.rename, ihA, iha, ihb]
  | lam A b ihA ihb =>
      simp only [CTm.subst, CTm.rename, ihA]
      rw [← ihb (liftRen ρ)]
      apply congrArg (fun body => (CTm.rename ρ A).lam body)
      apply CTm.subst_ext
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · rfl
  | app f a ihf iha =>
      simp only [CTm.subst, CTm.rename, ihf, iha]
  | pair a b iha ihb =>
      simp only [CTm.subst, CTm.rename, iha, ihb]
  | fst p ih =>
      simp only [CTm.subst, CTm.rename, ih]
  | snd p ih =>
      simp only [CTm.subst, CTm.rename, ih]
  | refl a ih =>
      simp only [CTm.subst, CTm.rename, ih]

/-! ## The arguments of the left side -/

/-- The motive and the methods: the first `1 + c` metavariables. -/
def recPrefix (c a : Nat) : List (Tm Head (1 + c + a)) :=
  (metaVars (1 + c + a)).take (1 + c)

/-- The fields: the last `a` metavariables. -/
def fieldArgs (c a : Nat) : List (Tm Head (1 + c + a)) :=
  (metaVars (1 + c + a)).drop (1 + c)

/-- The constructor applied to the field metavariables. -/
def scrutinee (k : DeclName) (c a : Nat) : Tm Head (1 + c + a) :=
  Normalization.appSpine (.const k) (fieldArgs c a)

/-- The recursor's spine: motive, methods, and the constructor application. -/
def recSpine (k : DeclName) (c a : Nat) : List (Tm Head (1 + c + a)) :=
  recPrefix c a ++ [scrutinee k c a]

theorem iotaLeft_spine (rec k : DeclName) (c a : Nat) :
    iotaLeft (Head := Head) rec k c a =
      Normalization.appSpine (.const rec) (recSpine k c a) := by
  unfold iotaLeft Normalization.recApp recSpine scrutinee recPrefix fieldArgs
  rfl

theorem recPrefix_length (c a : Nat) : (recPrefix (Head := Head) c a).length = 1 + c := by
  unfold recPrefix
  exact List.length_take_of_le (by rw [length_metaVars]; exact Nat.le_add_right (1 + c) a)

theorem fieldArgs_length (c a : Nat) : (fieldArgs (Head := Head) c a).length = a := by
  unfold fieldArgs
  rw [List.length_drop, length_metaVars, Nat.add_sub_cancel_left]

theorem recSpine_length (k : DeclName) (c a : Nat) :
    (recSpine (Head := Head) k c a).length = c + 2 := by
  unfold recSpine
  rw [List.length_append, List.length_singleton, recPrefix_length, one_add_add_one]

theorem metaVars_get? {N r : Nat} (hr : r < N) :
    (metaVars (Head := Head) N)[r]? = some (Tm.var (Head := Head) (metaIdx N r hr)) := by
  unfold metaVars
  have hfin : r < (List.finRange N).length := by rw [List.length_finRange]; exact hr
  rw [List.getElem?_map, List.getElem?_reverse hfin, List.length_finRange]
  have hidx : N - 1 - r < (List.finRange N).length := by
    rw [List.length_finRange]
    exact index_lt N r hr
  rw [getElem?_pos (List.finRange N) (N - 1 - r) hidx, List.getElem_finRange]
  apply congrArg some
  apply congrArg (Tm.var (Head := Head))
  apply Fin.ext
  rfl

theorem recPrefix_get? (c a r : Nat) (hr : r < 1 + c) :
    (recPrefix (Head := Head) c a)[r]? =
      some (Tm.var (Head := Head)
        (metaIdx (1 + c + a) r (Nat.lt_of_lt_of_le hr (Nat.le_add_right (1 + c) a)))) := by
  unfold recPrefix
  rw [List.getElem?_take_of_lt hr,
    metaVars_get? (Nat.lt_of_lt_of_le hr (Nat.le_add_right (1 + c) a))]

theorem fieldArgs_get? (c a p : Nat) (hp : p < a) :
    (fieldArgs (Head := Head) c a)[p]? =
      some (Tm.var (Head := Head) (fieldIdx c a p hp)) := by
  unfold fieldArgs
  have hpN : (1 + c) + p < 1 + c + a := Nat.add_lt_add_left hp (1 + c)
  rw [List.getElem?_drop, metaVars_get? hpN]
  apply congrArg some
  apply congrArg (Tm.var (Head := Head))
  apply Fin.ext
  exact field_var_val c a p hp

theorem recSpine_prefix_get (k : DeclName) (c a q : Nat) (hq : q < 1 + c) :
    (recSpine (Head := Head) k c a)[q]? =
      some (Tm.var (Head := Head)
        (metaIdx (1 + c + a) q (Nat.lt_of_lt_of_le hq (Nat.le_add_right (1 + c) a)))) := by
  have hqlen : q < (recPrefix (Head := Head) c a).length := by rw [recPrefix_length]; exact hq
  rw [show recSpine (Head := Head) k c a =
        recPrefix (Head := Head) c a ++ [scrutinee (Head := Head) k c a] from rfl,
    getElem?_append_left (recPrefix (Head := Head) c a) [scrutinee (Head := Head) k c a] q hqlen,
    recPrefix_get? c a q hq]

theorem recSpine_last_get (k : DeclName) (c a : Nat) :
    (recSpine (Head := Head) k c a)[c + 1]? = some (scrutinee (Head := Head) k c a) := by
  have hlen : (recPrefix (Head := Head) c a).length = c + 1 := by
    rw [recPrefix_length, Nat.add_comm]
  rw [← hlen]
  exact getElem?_concat_last (recPrefix (Head := Head) c a) (scrutinee (Head := Head) k c a)

theorem listSub_recSpine (k : DeclName) (c a q : Nat) (hq : q ≤ 1 + c) (i : Fin q) :
    listSub q (recSpine (Head := Head) k c a) i =
      .var (shiftBy (Nat.le_trans hq (Nat.le_add_right (1 + c) a)) i) := by
  have hN : q ≤ 1 + c + a := Nat.le_trans hq (Nat.le_add_right (1 + c) a)
  have hi : i.val + 1 ≤ q := Nat.succ_le_of_lt i.isLt
  have hrlt : q - (i.val + 1) < q := Nat.sub_lt_of_pos_le (Nat.zero_lt_succ i.val) hi
  have hidx : q - 1 - i.val = q - (i.val + 1) := by
    rw [Nat.sub_sub]
    exact congrArg (fun k => q - k) (Nat.add_comm 1 i.val)
  have hrq : q - 1 - i.val < q := hidx ▸ hrlt
  have hpre : q - 1 - i.val < (recPrefix (Head := Head) c a).length := by
    rw [recPrefix_length]
    exact Nat.lt_of_lt_of_le hrq hq
  have hrTake : q - 1 - i.val < 1 + c := by
    rw [← recPrefix_length c a]
    exact hpre
  unfold listSub recSpine
  rw [getD_append_left (recPrefix (Head := Head) c a) [scrutinee (Head := Head) k c a]
      (q - 1 - i.val) Normalization.defaultTm hpre,
    List.getD_eq_getElem?_getD, recPrefix_get? c a (q - 1 - i.val) hrTake, Option.getD_some]
  apply congrArg Tm.var
  apply Fin.ext
  exact index_shift (1 + c + a) q i.val i.isLt hN

theorem argType_recSpine (entry : (j : Nat) → Tm Head j) (k : DeclName) (c a q : Nat)
    (hq : q ≤ 1 + c) :
    argType entry (recSpine k c a) q =
      (liftTm (entry q)).rename (shiftBy (Nat.le_trans hq (Nat.le_add_right (1 + c) a))) := by
  unfold argType
  rw [← subst_varRen]
  apply CTm.subst_ext
  intro i
  unfold argSub
  rw [listSub_recSpine k c a q hq i]
  rfl

theorem argType_ctorEntry {N : Nat} (T : DeclName) (fields : List (Field Head))
    (ts : List (Tm Head N)) (p : Nat) :
    argType (Normalization.ctorEntry T fields) ts p =
      CTm.liftClosed (liftTm ((fields.getD p .recursive).type T)) := by
  unfold argType Normalization.ctorEntry
  rw [liftTm_liftClosed, CTm.subst_liftClosed]

theorem iotaEntry_of_le {T : DeclName} {v : Head} {ctors : List (DeclName × List (Field Head))}
    {fields : List (Field Head)} {q : Nat} (hq : q ≤ ctors.length) :
    iotaEntry T v ctors fields q = Normalization.recEntry T v ctors q := by
  unfold iotaEntry
  rw [if_pos hq]

theorem iotaEntry_field {T : DeclName} {v : Head} {ctors : List (DeclName × List (Field Head))}
    {fields : List (Field Head)} {p : Nat} (_hp : p < fields.length) :
    iotaEntry T v ctors fields (ctors.length + 1 + p) =
      Presentation.liftClosed ((fields.getD p .recursive).type T) := by
  unfold iotaEntry
  have hgt : ¬ ctors.length + 1 + p ≤ ctors.length := by
    intro hle
    have hsucc : ctors.length + 1 ≤ ctors.length := Nat.le_trans (Nat.le_add_right _ p) hle
    exact Nat.lt_irrefl _ (Nat.lt_of_succ_le hsucc)
  rw [if_neg hgt, Nat.add_sub_cancel_left]

/-- A field entry is closed, so renaming it into the rule's context leaves the field's type. -/
theorem iotaEntry_field_at {T : DeclName} {v : Head}
    {ctors : List (DeclName × List (Field Head))} {fields : List (Field Head)}
    {q p : Nat} (hq : q < 1 + ctors.length + fields.length) (hp : p < fields.length)
    (hs : q = ctors.length + 1 + p) :
    liftTm (Presentation.rename (shiftBy (Nat.le_of_lt hq)) (iotaEntry T v ctors fields q)) =
      CTm.liftClosed (liftTm ((fields.getD p .recursive).type T)) := by
  subst hs
  rw [iotaEntry_field hp, rename_liftClosed, liftTm_liftClosed]

/-- Lookup in the telescope of a computation rule, at a metavariable. -/
theorem iota_lookup {T : DeclName} {v : Head} {ctors : List (DeclName × List (Field Head))}
    {fields : List (Field Head)} (j : Fin (1 + ctors.length + fields.length)) :
    (liftCtx (iotaTele T v ctors fields)).lookup j =
      liftTm (Presentation.rename
        (shiftBy (Nat.le_of_lt (index_lt _ j.val j.isLt)))
        (iotaEntry T v ctors fields ((1 + ctors.length + fields.length) - 1 - j.val))) := by
  have hq : (1 + ctors.length + fields.length) - 1 - j.val <
      1 + ctors.length + fields.length := index_lt _ j.val j.isLt
  have hlook := telescope_lookup (iotaEntry T v ctors fields)
    (1 + ctors.length + fields.length)
    ((1 + ctors.length + fields.length) - 1 - j.val) hq
  rw [metaIdx_back j] at hlook
  rw [liftCtx_lookup, iotaTele, hlook]

/-! ## Occurrences -/

theorem multiplicity_const {n : Nat} (v : Fin n) (c : DeclName) :
    AlgebraicSchema.variableMultiplicity v (.const c : Tm Head n) = 0 := rfl

theorem multiplicity_spine_zero {n : Nat} (v : Fin n) (f : Tm Head n) (ts : List (Tm Head n))
    (hf : AlgebraicSchema.variableMultiplicity v f = 0)
    (ha : ∀ a ∈ ts, AlgebraicSchema.variableMultiplicity v a = 0) :
    AlgebraicSchema.variableMultiplicity v (Normalization.appSpine f ts) = 0 := by
  induction ts generalizing f with
  | nil =>
      rw [Normalization.appSpine_nil]
      exact hf
  | cons a as ih =>
      rw [Normalization.appSpine_cons]
      refine ih (.app f a) ?_ (fun b hb => ha b (List.mem_cons_of_mem a hb))
      rw [AlgebraicSchema.variableMultiplicity, hf, ha a List.mem_cons_self, Nat.zero_add]

theorem recSpine_fo (k : DeclName) (c a : Nat) :
    ∀ t ∈ recSpine (Head := Head) k c a, firstOrder t = true := by
  intro t ht
  rw [show recSpine (Head := Head) k c a =
      recPrefix (Head := Head) c a ++ [scrutinee (Head := Head) k c a] from rfl] at ht
  rcases List.mem_append.mp ht with pre | last
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take pre)
    simp only [firstOrder]
  · obtain rfl := List.mem_singleton.mp last
    unfold scrutinee
    refine firstOrder_appSpine (.const k) (fieldArgs c a) rfl ?_
    intro y hy
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop hy)
    simp only [firstOrder]

theorem fieldArgs_fo (c a : Nat) : ∀ t ∈ fieldArgs (Head := Head) c a, firstOrder t = true := by
  intro t ht
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop ht)
  simp only [firstOrder]

theorem multiplicity_scrutinee_high (k : DeclName) (c a : Nat) (v : Fin (1 + c + a))
    (hv : a ≤ v.val) :
    AlgebraicSchema.variableMultiplicity v (scrutinee (Head := Head) k c a) = 0 := by
  unfold scrutinee
  refine multiplicity_spine_zero v (.const k) (fieldArgs (Head := Head) c a)
    (multiplicity_const v k) ?_
  intro t ht
  obtain ⟨r, hr⟩ := exists_getElem?_of_mem ht
  have hlt := lt_of_getElem?_some hr
  rw [fieldArgs_length] at hlt
  have heq := hr.symm.trans (fieldArgs_get? c a r hlt)
  injection heq with heq
  rw [heq]
  apply variableMultiplicity_var_ne
  intro same
  exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (small_lt a r hlt) hv) (congrArg Fin.val same)

theorem alone_high (k : DeclName) (c a q : Nat) (hq : q ≤ c) (v : Fin (1 + c + a))
    (hv : v.val = (1 + c + a) - 1 - q)
    (j' : Nat) (t' : Tm Head (1 + c + a)) (hne : j' ≠ q)
    (ht : (recSpine k c a)[j']? = some t') :
    AlgebraicSchema.variableMultiplicity v t' = 0 := by
  have hlt := lt_of_getElem?_some ht
  rw [recSpine_length] at hlt
  cases hdec : decide (j' ≤ c) with
  | true =>
      have hjle : j' ≤ c := of_decide_eq_true hdec
      have hjlt : j' < 1 + c := by
        rw [Nat.add_comm]
        exact Nat.lt_add_one_of_le hjle
      have heq := ht.symm.trans (recSpine_prefix_get k c a j' hjlt)
      injection heq with heq
      rw [heq]
      apply variableMultiplicity_var_ne
      intro same
      have hvals := congrArg Fin.val same
      have hpos : j' = q := by
        have hqlt : q < 1 + c + a :=
          Nat.lt_of_le_of_lt hq (Nat.lt_of_lt_of_le
            (by rw [Nat.add_comm]; exact Nat.lt_add_one c) (Nat.le_add_right (1 + c) a))
        have hjN : j' < 1 + c + a := Nat.lt_of_lt_of_le hjlt (Nat.le_add_right (1 + c) a)
        apply metaIdx_inj hjN hqlt
        apply Fin.ext
        rw [hvals, hv]
        rfl
      exact hne hpos
  | false =>
      have hgt : c < j' := (Nat.not_le).mp (of_decide_eq_false hdec)
      have hle : j' ≤ c + 1 := Nat.le_of_lt_add_one hlt
      have hj : j' = c + 1 := Nat.le_antisymm hle (Nat.succ_le_of_lt hgt)
      subst hj
      have heq := ht.symm.trans (recSpine_last_get k c a)
      injection heq with heq
      rw [heq]
      have hvHigh : a ≤ v.val := by
        rw [hv]
        exact prefix_val_ge c a q (by rw [Nat.add_comm]; exact Nat.lt_add_one_of_le hq)
      exact multiplicity_scrutinee_high k c a v hvHigh

theorem alone_low (k : DeclName) (c a : Nat) (v : Fin (1 + c + a)) (hv : v.val < a)
    (j' : Nat) (t' : Tm Head (1 + c + a)) (hne : j' ≠ c + 1)
    (ht : (recSpine k c a)[j']? = some t') :
    AlgebraicSchema.variableMultiplicity v t' = 0 := by
  have hlt := lt_of_getElem?_some ht
  rw [recSpine_length] at hlt
  have hle : j' ≤ c + 1 := Nat.le_of_lt_add_one hlt
  have hjle : j' ≤ c := Nat.le_of_lt_add_one (Nat.lt_of_le_of_ne hle hne)
  have hjlt : j' < 1 + c := by
    rw [Nat.add_comm]
    exact Nat.lt_add_one_of_le hjle
  have heq := ht.symm.trans (recSpine_prefix_get k c a j' hjlt)
  injection heq with heq
  rw [heq]
  apply variableMultiplicity_var_ne
  intro same
  exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hv (prefix_val_ge c a j' hjlt))
    (congrArg Fin.val same).symm

theorem alone_field (c a p : Nat) (hp : p < a) (v : Fin (1 + c + a))
    (hv : v = fieldIdx c a p hp) (j' : Nat) (t' : Tm Head (1 + c + a)) (hne : j' ≠ p)
    (ht : (fieldArgs c a)[j']? = some t') :
    AlgebraicSchema.variableMultiplicity v t' = 0 := by
  have hlt := lt_of_getElem?_some ht
  rw [fieldArgs_length] at hlt
  have heq := ht.symm.trans (fieldArgs_get? c a j' hlt)
  injection heq with heq
  rw [heq]
  apply variableMultiplicity_var_ne
  intro same
  have hvals := congrArg Fin.val (hv.symm.trans same.symm)
  have hle1 : p ≤ a - 1 := Nat.le_sub_of_add_le (Nat.succ_le_of_lt hp)
  have hle2 : j' ≤ a - 1 := Nat.le_sub_of_add_le (Nat.succ_le_of_lt hlt)
  exact hne (sub_left_inj hle1 hle2 hvals).symm

/-! ## Elaborated declarations -/

theorem elab_recursor {T : DeclName} {u : Head} {ctors : List (DeclName × List (Field Head))}
    {rec : DeclName} {v : Head} (distinct : DistinctNames T ctors rec)
    (free : FieldsLamFree ctors) :
    elabDeclarations (inductiveDecls T u ctors rec v) rec =
      some (liftTm (closeType
        (Normalization.ofEntries (Normalization.recEntry T v ctors) (ctors.length + 2))
        (Normalization.recBody ctors.length))) := by
  rw [elabDeclarations_lamFree _ (inductiveDecls_rec distinct) (lamFree_recType T v free)]
  rfl

theorem elab_constructor {T : DeclName} {u : Head} {ctors : List (DeclName × List (Field Head))}
    {rec : DeclName} {v : Head} (distinct : DistinctNames T ctors rec)
    (free : FieldsLamFree ctors) {i : Nat} {k : DeclName} {fields : List (Field Head)}
    (entry : ctors[i]? = some (k, fields)) :
    elabDeclarations (inductiveDecls T u ctors rec v) k =
      some (liftTm (closeType
        (Normalization.ofEntries (Normalization.ctorEntry T fields) fields.length)
        (.const T))) := by
  rw [elabDeclarations_lamFree _ (inductiveDecls_ctor distinct entry)
    (lamFree_ctorType T (fun F mem => free _ (List.mem_of_getElem? entry) F mem))]
  rfl

/-! ## The knowledge of the left side -/

/-- **The knowledge of the left side of a computation rule** is the telescope of
its metavariables. This is the hypothesis `known` of `iota_equal`. -/
theorem iotaLeft_known {T : DeclName} {u : Head} {ctors : List (DeclName × List (Field Head))}
    {rec : DeclName} {v : Head} (distinct : DistinctNames T ctors rec)
    (free : FieldsLamFree ctors) {i : Nat} {k : DeclName} {fields : List (Field Head)}
    (entry : ctors[i]? = some (k, fields))
    (j : Fin (1 + ctors.length + fields.length)) :
    patternKnowledge (elabDeclarations (inductiveDecls T u ctors rec v)) none
        (iotaLeft rec k ctors.length fields.length) j =
      some ((liftCtx (iotaTele T v ctors fields)).lookup j) := by
  let c := ctors.length
  let a := fields.length
  rw [iotaLeft_spine]
  have hRec := elab_recursor (T := T) (u := u) (ctors := ctors) (rec := rec) (v := v)
    distinct free
  have hCtor := elab_constructor (T := T) (u := u) (ctors := ctors) (rec := rec) (v := v)
    distinct free entry
  cases hbranch : decide (j.val < a) with
  | false =>
      have hge : a ≤ j.val := (Nat.not_lt).mp (of_decide_eq_false hbranch)
      have hqle : (1 + c + a) - 1 - j.val ≤ c := high_position_le c a j.val hge
      have hqlt : (1 + c + a) - 1 - j.val < 1 + c :=
        Nat.lt_of_le_of_lt hqle (by rw [Nat.add_comm]; exact Nat.lt_add_one c)
      set q := (1 + c + a) - 1 - j.val
      have hlen : (recSpine (Head := Head) k c a).length ≤ c + 2 :=
        Nat.le_of_eq (recSpine_length k c a)
      have ht0 := recSpine_prefix_get (Head := Head) k c a q hqlt
      have hv : metaIdx (1 + c + a) q (Nat.lt_of_lt_of_le hqlt (Nat.le_add_right (1 + c) a)) = j := by
        apply Fin.ext
        exact index_back (1 + c + a) j.val j.isLt
      rw [hv] at ht0
      have alone := alone_high (Head := Head) k c a q hqle j (congrArg Fin.val hv).symm 
      rw [spine_knowledge_var (elabDeclarations (inductiveDecls T u ctors rec v)) rec (c + 2)
          (Normalization.recEntry T v ctors) (Normalization.recBody c) hRec
          (recSpine k c a) (recSpine_fo k c a) hlen q j ht0 alone none,
        argType_recSpine (Normalization.recEntry T v ctors) k c a q (Nat.le_of_lt hqlt),
        iota_lookup, liftTm_rename, iotaEntry_of_le hqle]
  | true =>
      have hlow : j.val < a := of_decide_eq_true hbranch
      set p := a - 1 - j.val
      have hp : p < a := small_lt a j.val hlow
      have hqEq : (1 + c + a) - 1 - j.val = c + 1 + p := field_position c a j.val hlow
      have hvIdx : fieldIdx c a p hp = j := by
        apply Fin.ext
        show a - 1 - p = j.val
        rw [show p = a - 1 - j.val from rfl]
        exact Nat.sub_sub_self (Nat.le_sub_of_add_le (Nat.succ_le_of_lt hlow))
      have hlen : (recSpine (Head := Head) k c a).length ≤ c + 2 :=
        Nat.le_of_eq (recSpine_length k c a)
      have htScrut : (recSpine (Head := Head) k c a)[c + 1]? =
          some (scrutinee (Head := Head) k c a) := recSpine_last_get k c a
      have aloneRec := alone_low (Head := Head) k c a j hlow
      rw [spine_knowledge (elabDeclarations (inductiveDecls T u ctors rec v)) rec (c + 2)
          (Normalization.recEntry T v ctors) (Normalization.recBody c) hRec
          (recSpine k c a) (recSpine_fo k c a) hlen (c + 1) (scrutinee k c a) htScrut j aloneRec
          none]
      rw [show scrutinee k c a = Normalization.appSpine (.const k) (fieldArgs c a) from rfl,
        patternKnowledge_spine_expected (elabDeclarations (inductiveDecls T u ctors rec v)) k
          (fieldArgs c a)]
      have hflen : (fieldArgs (Head := Head) c a).length ≤ a :=
        Nat.le_of_eq (fieldArgs_length c a)
      have htField : (fieldArgs (Head := Head) c a)[p]? = some (Tm.var (Head := Head) j) := by
        rw [fieldArgs_get? c a p hp, hvIdx]
      have aloneF := alone_field (Head := Head) c a p hp j hvIdx.symm
      rw [spine_knowledge_var (elabDeclarations (inductiveDecls T u ctors rec v)) k a
          (Normalization.ctorEntry T fields) (.const T) hCtor
          (fieldArgs c a) (fieldArgs_fo c a) hflen p j htField aloneF none,
        argType_ctorEntry, iota_lookup]
      apply congrArg some
      exact (iotaEntry_field_at (index_lt _ j.val j.isLt) hp hqEq).symm

/-- **The type the left side of a computation rule synthesizes** is the motive at the
constructor applied to its fields, under every table of declared types that declares the
recursor as the declaration does: the declaration's own, or that of a package containing it. -/
theorem iotaLeft_type {decls : DeclName → Option (CTm Head 0)} {T : DeclName} {v : Head}
    {ctors : List (DeclName × List (Field Head))} {rec : DeclName}
    (recDeclared : decls rec = some (liftTm (closeType
      (Normalization.ofEntries (Normalization.recEntry T v ctors) (ctors.length + 2))
      (Normalization.recBody ctors.length))))
    (k : DeclName) (a : Nat) :
    leftType decls (iotaLeft rec k ctors.length a) =
      some (liftTm (iotaTarget k ctors.length a)) := by
  unfold leftType
  rw [iotaLeft_spine]
  obtain ⟨R, hR, synth⟩ := spine_type decls rec (ctors.length + 2)
    (Normalization.recEntry T v ctors) (Normalization.recBody ctors.length) recDeclared
    (recSpine k ctors.length a) (recSpine_fo k ctors.length a)
    (Nat.le_of_eq (recSpine_length k ctors.length a))
  rw [synth]
  clear synth
  revert R
  rw [recSpine_length]
  intro R hR
  obtain rfl := hR.eq_body
  apply congrArg some
  show CTm.app
      (liftTm ((recSpine k ctors.length a).getD (ctors.length + 2 - 1 - (ctors.length + 1))
        Normalization.defaultTm))
      (liftTm ((recSpine k ctors.length a).getD (ctors.length + 2 - 1 - 0)
        Normalization.defaultTm)) = _
  rw [show ctors.length + 2 - 1 - (ctors.length + 1) = 0 by omega,
    show ctors.length + 2 - 1 - 0 = ctors.length + 1 by omega,
    getD_of_getElem? (recSpine_prefix_get k ctors.length a 0 (by omega)),
    getD_of_getElem? (recSpine_last_get k ctors.length a)]
  have motive : metaIdx (1 + ctors.length + a) 0 (by omega) = ⟨ctors.length + a, by omega⟩ :=
    Fin.ext (show 1 + ctors.length + a - 1 - 0 = ctors.length + a by omega)
  rw [motive]
  rfl

/-! ## Examples -/

namespace IotaExamples

def tyName : DeclName := Lean.Name.mkSimple "Nat"

def ctorName : DeclName := Lean.Name.mkSimple "succ"

def recName : DeclName := Lean.Name.mkSimple "natRec"

def ctors {Head : Type} : List (DeclName × List (Field Head)) :=
  [(ctorName, [.recursive])]

theorem ex_entry {Head : Type} :
    (ctors (Head := Head))[0]? = some (ctorName, [.recursive]) := rfl

theorem name_ne {a b : String} (h : a ≠ b) :
    Lean.Name.mkSimple a ≠ Lean.Name.mkSimple b := by
  intro eq
  unfold Lean.Name.mkSimple at eq
  injection eq with _ hs
  exact h hs

theorem exDistinct {Head : Type} : DistinctNames tyName (ctors (Head := Head)) recName where
  ctorsNodup := by
    unfold ctors
    simp only [List.map_cons, List.map_nil]
    exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  typeNotCtor := by
    intro h
    unfold ctors at h
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
    exact name_ne (by decide) h.symm
  recNotType := name_ne (by decide)
  recNotCtor := by
    intro h
    unfold ctors at h
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at h
    exact name_ne (by decide) h.symm

theorem exFree {Head : Type} : FieldsLamFree (ctors (Head := Head)) := by
  intro entry mem F closed
  unfold ctors at mem
  obtain rfl := List.mem_singleton.mp mem
  cases List.mem_cons.mp closed with
  | inl h => cases h
  | inr h => cases h

theorem ex_arity :
    (1 + (ctors (Head := Head)).length + [(@Field.recursive Head)].length) = 3 := by
  unfold ctors
  rfl

/-- A numeral of the three-variable rule, as an index of that rule. -/
def exVar (k : Fin 3) :
    Fin (1 + (ctors (Head := Head)).length + [(@Field.recursive Head)].length) :=
  Fin.cast ex_arity.symm k

private theorem ex_index (k : Fin 3) :
    (1 + (ctors (Head := Head)).length + [(@Field.recursive Head)].length) - 1 -
      (exVar (Head := Head) k).val = 2 - k.val := by
  unfold exVar
  rw [Fin.val_cast, ex_arity]

/-- The motive entry, once its position is known to be the first. -/
theorem motive_entry {v : Head} {q : Nat}
    (hq : q < 1 + (ctors (Head := Head)).length + [(@Field.recursive Head)].length)
    (h0 : q = 0) :
    liftTm (Presentation.rename (shiftBy (Nat.le_of_lt hq))
        (iotaEntry tyName v ctors [(@Field.recursive Head)] q)) =
      CTm.liftClosed (liftTm (Normalization.motiveTy tyName v)) := by
  subst h0
  rw [iotaEntry_of_le (Nat.zero_le _), Normalization.recEntry, rename_from_closed,
    liftTm_liftClosed]

/-- The motive metavariable is known at the type of motives. -/
theorem motive_known (u v : Head) :
    patternKnowledge (elabDeclarations (inductiveDecls tyName u ctors recName v)) none
        (iotaLeft recName ctorName ctors.length [(@Field.recursive Head)].length) (exVar 2) =
      some (CTm.liftClosed (liftTm (Normalization.motiveTy tyName v))) := by
  rw [iotaLeft_known exDistinct exFree ex_entry (exVar 2)]
  apply congrArg some
  rw [iota_lookup]
  exact motive_entry (index_lt _ (exVar 2).val (exVar 2).isLt)
    (ex_index (Head := Head) (2 : Fin 3))

/-- The method entry, once its position is known to be the second. -/
theorem method_entry {v : Head} {q : Nat}
    (hq : q < 1 + (ctors (Head := Head)).length + [(@Field.recursive Head)].length)
    (h1 : q = 1) :
    liftTm (Presentation.rename (shiftBy (Nat.le_of_lt hq))
        (iotaEntry tyName v ctors [(@Field.recursive Head)] q)) =
      (liftTm (Normalization.recEntry tyName v ctors 1)).rename
        (shiftBy (Nat.le_of_lt (by
          rw [ex_arity]
          exact Nat.lt_trans (Nat.lt_succ_self 1) (Nat.lt_succ_self 2)))) := by
  subst h1
  rw [iotaEntry_of_le (by unfold ctors; exact Nat.le_refl _), liftTm_rename]

/-- The method metavariable is known at the method's entry, shifted by the one entry after it. -/
theorem method_known (u v : Head) :
    patternKnowledge (elabDeclarations (inductiveDecls tyName u ctors recName v)) none
        (iotaLeft recName ctorName ctors.length [(@Field.recursive Head)].length) (exVar 1) =
      some ((liftTm (Normalization.recEntry tyName v ctors 1)).rename
        (shiftBy (Nat.le_of_lt (by
          rw [ex_arity]
          exact Nat.lt_trans (Nat.lt_succ_self 1) (Nat.lt_succ_self 2))))) := by
  rw [iotaLeft_known exDistinct exFree ex_entry (exVar 1)]
  apply congrArg some
  rw [iota_lookup]
  exact method_entry (index_lt _ (exVar 1).val (exVar 1).isLt)
    (ex_index (Head := Head) (1 : Fin 3))

/-- The field entry, once its position is known to be the field slot. -/
theorem field_entry {v : Head} {q : Nat}
    (hq : q < 1 + (ctors (Head := Head)).length + [(@Field.recursive Head)].length)
    (hs : q = (ctors (Head := Head)).length + 1 + 0) :
    liftTm (Presentation.rename (shiftBy (Nat.le_of_lt hq))
        (iotaEntry tyName v ctors [(@Field.recursive Head)] q)) =
      CTm.liftClosed (liftTm (.const tyName)) := by
  subst hs
  rw [iotaEntry_field (Nat.zero_lt_succ 0), rename_liftClosed, liftTm_liftClosed]
  unfold List.getD
  rw [List.getElem?_cons_zero, Option.getD_some]
  unfold Field.type
  rfl

/-- The field metavariable is known at the field's type, the declared type. -/
theorem field_known (u v : Head) :
    patternKnowledge (elabDeclarations (inductiveDecls tyName u ctors recName v)) none
        (iotaLeft recName ctorName ctors.length [(@Field.recursive Head)].length) (exVar 0) =
      some (CTm.liftClosed (liftTm (.const tyName))) := by
  rw [iotaLeft_known exDistinct exFree ex_entry (exVar 0)]
  apply congrArg some
  rw [iota_lookup]
  exact field_entry (index_lt _ (exVar 0).val (exVar 0).isLt) (by
    rw [ex_index (Head := Head) 0]
    unfold ctors
    rfl)

section Repeated

def twiceEntry : (j : Nat) → Tm Head j
  | 0 => .const (Lean.Name.mkSimple "left")
  | 1 => .const (Lean.Name.mkSimple "right")
  | _ + 2 => .const (Lean.Name.mkSimple "right")

def twiceC : Tm Head 2 := .const (Lean.Name.mkSimple "C")

def twiceF : DeclName := Lean.Name.mkSimple "f"

def twiceDecls (c : DeclName) : Option (CTm Head 0) :=
  if c = twiceF then some (liftTm (closeType (Normalization.ofEntries twiceEntry 2) twiceC))
  else none

theorem twiceDeclared :
    (twiceDecls twiceF : Option (CTm Head 0)) =
      some (liftTm (closeType (Normalization.ofEntries twiceEntry 2) twiceC)) := by
  unfold twiceDecls
  exact if_pos rfl

def twiceTs : List (Tm Head 1) := [.var 0, .var 0]

def twicePrefix : List (Tm Head 1) := [.var 0]

theorem twice_arg_left :
    (argType twiceEntry twicePrefix 0 : CTm Head 1) =
      .const (Lean.Name.mkSimple "left") := by
  simp only [argType, twiceEntry, liftTm, CTm.annotateWith, CTm.subst]

theorem twice_arg_right :
    (argType twiceEntry twiceTs 1 : CTm Head 1) =
      .const (Lean.Name.mkSimple "right") := by
  simp only [argType, twiceEntry, liftTm, CTm.annotateWith, CTm.subst]

theorem twice_prefix_fo : ∀ t ∈ (twicePrefix : List (Tm Head 1)), firstOrder t = true := by
  intro t ht
  cases List.mem_singleton.mp ht
  simp only [firstOrder]

theorem twice_prefix_alone (j' : Nat) (t' : Tm Head 1) (hne : j' ≠ 0)
    (ht : twicePrefix[j']? = some t') :
    AlgebraicSchema.variableMultiplicity (0 : Fin 1) t' = 0 := by
  have hlt := lt_of_getElem?_some ht
  exact absurd (Nat.lt_one_iff.mp hlt) hne

theorem twice_const_ne :
    (.const (Lean.Name.mkSimple "left") : CTm Head 1) ≠
      .const (Lean.Name.mkSimple "right") := by
  intro h
  injection h with _ hn
  unfold Lean.Name.mkSimple at hn
  injection hn with _ hs
  exact absurd hs (by decide)

/-- A metavariable that occurs twice is known at the first entry. The merge keeps
that `some`, and the second copy adds nothing. -/
theorem twice_knowledge (expected : Option (CTm Head 1)) :
    patternKnowledge twiceDecls expected
        (Normalization.appSpine (.const twiceF) twiceTs) (0 : Fin 1) =
      some (.const (Lean.Name.mkSimple "left")) := by
  have hlen : (twicePrefix : List (Tm Head 1)).length ≤ 2 := by
    simp only [twicePrefix, List.length_cons, List.length_nil]
    exact Nat.le_succ 1
  have ht : (twicePrefix : List (Tm Head 1))[0]? = some (.var (0 : Fin 1)) := rfl
  have hprefix := spine_knowledge_var twiceDecls twiceF 2 twiceEntry twiceC twiceDeclared
    twicePrefix twice_prefix_fo hlen 0 (0 : Fin 1) ht twice_prefix_alone expected
  have hsame := patternKnowledge_spine_expected twiceDecls twiceF twicePrefix none expected
    (0 : Fin 1)
  rw [show twiceTs = twicePrefix ++ [.var (0 : Fin 1)] from rfl, Normalization.appSpine_concat,
    patternKnowledge_app, merge_left_of_some (hsame.trans hprefix), twice_arg_left]

/-- At the second copy the equation that would give the second entry is false. -/
theorem twice_second_fails (expected : Option (CTm Head 1)) :
    patternKnowledge twiceDecls expected
        (Normalization.appSpine (.const twiceF) twiceTs) (0 : Fin 1) ≠
      patternKnowledge twiceDecls (some (argType twiceEntry twiceTs 1)) (.var (0 : Fin 1))
        (0 : Fin 1) := by
  intro h
  rw [twice_knowledge expected, twice_arg_right] at h
  simp only [patternKnowledge] at h
  injection h with h
  exact twice_const_ne h

end Repeated

end IotaExamples

section ContainingPackages

open Normalization
open UniverseLevel (LevelOrder)

/-! ## Containment of packages -/

/-- Containment of packages composes. -/
theorem ChurchRulesSub.trans {R₁ R₂ R₃ : Rules Head} {Q₁ : ChurchRules R₁} {Q₂ : ChurchRules R₂}
    {Q₃ : ChurchRules R₃} (first : ChurchRulesSub Q₁ Q₂) (second : ChurchRulesSub Q₂ Q₃) :
    ChurchRulesSub Q₁ Q₃ where
  headTyping := fun typing => second.headTyping (first.headTyping typing)
  isUniverse := fun isUniverse => second.isUniverse (first.isUniverse isUniverse)
  join := fun join => second.join (first.join join)
  cumulative := fun below => second.cumulative (first.cumulative below)
  headEq := fun equal => second.headEq (first.headEq equal)
  constantType := fun known => second.constantType (first.constantType known)
  computation := fun step => second.computation (first.computation step)
  requires := fun step required => by
    obtain ⟨middle, requiredMiddle, amongFirst⟩ := first.requires step required
    obtain ⟨last, requiredLast, amongMiddle⟩ :=
      second.requires (first.computation step) requiredMiddle
    exact ⟨last, requiredLast, fun premise member => amongFirst _ (amongMiddle _ member)⟩

/-- **The computation steps of a package are steps of another, with the same premises.** -/
structure StepsWithin {R₁ R₂ : Rules Head} (P : ChurchRules R₁) (Q : ChurchRules R₂) : Prop where
  step : ∀ {n : Nat} {l r : CTm Head n}, P.computation.step l r → Q.computation.step l r
  requires : ∀ {n : Nat} {l r : CTm Head n} {premises : List (CPremise Head n)},
    P.computation.step l r → P.computation.requires l r premises →
      Q.computation.requires l r premises

theorem StepsWithin.trans {R₁ R₂ R₃ : Rules Head} {Q₁ : ChurchRules R₁} {Q₂ : ChurchRules R₂}
    {Q₃ : ChurchRules R₃} (first : StepsWithin Q₁ Q₂) (second : StepsWithin Q₂ Q₃) :
    StepsWithin Q₁ Q₃ where
  step := fun step => second.step (first.step step)
  requires := fun step required => second.requires (first.step step) (first.requires step required)

/-- The steps of the first package of a sum are steps of the sum. -/
theorem StepsWithin.sum_left {R₁ R₂ : Rules Head} (P₁ : ChurchRules R₁) (P₂ : ChurchRules R₂) :
    StepsWithin P₁ (P₁.sum P₂) where
  step := .inl
  requires := fun step required => .inl ⟨step, required⟩

/-- The steps of the second package of a sum are steps of the sum. -/
theorem StepsWithin.sum_right {R₁ R₂ : Rules Head} (P₁ : ChurchRules R₁) (P₂ : ChurchRules R₂) :
    StepsWithin P₂ (P₁.sum P₂) where
  step := .inr
  requires := fun step required => .inr ⟨step, required⟩

/-- **A template typed in a package is typed in every package containing it**: the knowledge
and the type of its left side do not depend on the package, and the typing of its right side
persists. -/
theorem TemplateTyped.mono {R₁ R₂ : Rules Head} {P : ChurchRules R₁} {Q : ChurchRules R₂}
    (sub : ChurchRulesSub P Q) {decls : DeclName → Option (CTm Head 0)} {k : Nat}
    {L R' : Tm Head k} (typed : TemplateTyped P decls L R') : TemplateTyped Q decls L R' :=
  let ⟨Θ, T, known, left, right⟩ := typed
  ⟨Θ, T, known, left, right.mono sub⟩

/-! ## A declared datatype in a package that contains its declaration -/

section Within

variable {L : Type} [LevelOrder L] {R R' : Rules Head} (levels : LevelModel R L)
  (B : ChurchRules R) {T : DeclName} {u : Head} {ctors : List (DeclName × List (Field Head))}
  {rec : DeclName} {v : Head} {Q : ChurchRules R'}

include levels in
/-- **A constructor applied to listed terms of the types of its fields** is a term of the
declared type, in every package that contains the declaration. -/
theorem ctor_spine_typed_within (sub : ChurchRulesSub (withInductive B T u ctors rec v) Q)
    (hu : R.isUniverse u) (distinct : DistinctNames T ctors rec) (free : FieldsLamFree ctors)
    (new : NewNames B T ctors rec) (fieldsFormed : FieldsFormed B ctors) {i : Nat} {k : DeclName}
    {fields : List (Field Head)} (entry : ctors[i]? = some (k, fields)) {n : Nat}
    {Γ : CCtx Head n} {xs : List (Tm Head n)}
    (typed : List.Forall₂ (fun x (field : Field Head) =>
      CTyped Q Γ (liftTm x) (liftTm (field.type T)).liftClosed) xs fields) :
    CTyped Q Γ (liftTm (appSpine (.const k) xs)) (.const T) := by
  obtain ⟨length, pointwise⟩ := List.forall₂_iff_get.mp typed
  have function : CTyped Q Γ (liftTm (.const k : Tm Head n))
      (liftTm (closeType (ofEntries (ctorEntry T fields) fields.length) (.const T))).liftClosed :=
    CDerivable.mono sub (ctor_typed levels B hu distinct free new fieldsFormed entry)
  refine spine_typed (Q := Q) (ctorEntry T fields) fields.length (.const T) xs length function
    fun q x found => ?_
  obtain ⟨below, rfl⟩ := List.getElem?_eq_some_iff.mp found
  have belowFields : q < fields.length := length ▸ below
  show CTyped Q Γ (liftTm xs[q]) ((liftTm (ctorEntry T fields q)).subst (argSub xs q))
  rw [ctorEntry, liftTm_liftClosed, CTm.subst_liftClosed, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem belowFields]
  exact pointwise q below belowFields

include levels in
/-- **The typing of the recursor**, in every package that contains the declaration: applied
along a substitution typed along its telescope, the recursor has the motive's type at the
scrutinee. -/
theorem rec_applied_within (sub : ChurchRulesSub (withInductive B T u ctors rec v) Q)
    (hu : R.isUniverse u) (hv : R.isUniverse v) (distinct : DistinctNames T ctors rec)
    (free : FieldsLamFree ctors) (new : NewNames B T ctors rec)
    (fieldsFormed : FieldsFormed B ctors) {n : Nat} {Γ : CCtx Head n}
    {σ : CSub Head (ctors.length + 2) n}
    (typed : CSubstMor Q (liftCtx (recTele T v ctors)) Γ σ) :
    CTyped Q Γ (applyAlong σ (.const rec)) (.app (σ (Fin.last (ctors.length + 1))) (σ 0)) :=
  applyAlong_typed (recEntry T v ctors) (ctors.length + 2) (recBody ctors.length) σ typed
    (CDerivable.mono sub (rec_typed levels B hu hv distinct free new fieldsFormed))

include levels in
/-- **Both sides of an instance of a computation rule are typed**, in every package that
contains the declaration. -/
theorem iota_typed_within (sub : ChurchRulesSub (withInductive B T u ctors rec v) Q)
    (hu : R.isUniverse u) (hv : R.isUniverse v) (distinct : DistinctNames T ctors rec)
    (free : FieldsLamFree ctors) (new : NewNames B T ctors rec)
    (fieldsFormed : FieldsFormed B ctors) {i : Nat} {k : DeclName} {fields : List (Field Head)}
    (entry : ctors[i]? = some (k, fields)) {n : Nat} {Γ : CCtx Head n}
    (σ : CSub Head (1 + ctors.length + fields.length) n)
    (typed : CSubstMor Q (liftCtx (iotaTele T v ctors fields)) Γ σ) :
    CTyped Q Γ ((liftTm (iotaLeft rec k ctors.length fields.length)).subst σ)
        ((liftTm (iotaTarget k ctors.length fields.length)).subst σ) ∧
      CTyped Q Γ ((liftTm (iotaRight rec ctors.length i fields)).subst σ)
        ((liftTm (iotaTarget k ctors.length fields.length)).subst σ) :=
  ⟨CTyped.substitute
      (CDerivable.mono sub
        (iota_typed_metaVars levels B hu hv distinct free new fieldsFormed entry).1) typed,
    CTyped.substitute
      (CDerivable.mono sub
        (iota_typed_metaVars levels B hu hv distinct free new fieldsFormed entry).2) typed⟩

include levels in
/-- **The computation rule of the recursor, with the typings of its arguments as its only
premises**, in every package that contains the declaration and its steps: an instance typed
along the telescope of the rule's metavariables is an equality at the motive at the
constructor applied to its fields. -/
theorem iota_holds_within (sub : ChurchRulesSub (withInductive B T u ctors rec v) Q)
    (steps : StepsWithin (inductiveChurch R T u ctors rec v) Q)
    (hu : R.isUniverse u) (hv : R.isUniverse v) (distinct : DistinctNames T ctors rec)
    (free : FieldsLamFree ctors) (new : NewNames B T ctors rec)
    (fieldsFormed : FieldsFormed B ctors) {i : Nat} {k : DeclName} {fields : List (Field Head)}
    (entry : ctors[i]? = some (k, fields)) {n : Nat} {Γ : CCtx Head n}
    (σ : CSub Head (1 + ctors.length + fields.length) n)
    (typed : CSubstMor Q (liftCtx (iotaTele T v ctors fields)) Γ σ) :
    CEqual Q Γ ((liftTm (iotaLeft rec k ctors.length fields.length)).subst σ)
      ((liftTm (iotaRight rec ctors.length i fields)).subst σ)
      ((liftTm (iotaTarget k ctors.length fields.length)).subst σ) :=
  iota_equal R steps.step steps.requires entry (iotaLeft_known distinct free entry) σ typed
    (iota_typed_within levels B sub hu hv distinct free new fieldsFormed entry σ typed).1
    (iota_typed_within levels B sub hu hv distinct free new fieldsFormed entry σ typed).2

include levels in
/-- **The computation rule of the recursor in the package of the declaration.** -/
theorem iota_holds (hu : R.isUniverse u) (hv : R.isUniverse v)
    (distinct : DistinctNames T ctors rec) (free : FieldsLamFree ctors)
    (new : NewNames B T ctors rec) (fieldsFormed : FieldsFormed B ctors) {i : Nat}
    {k : DeclName} {fields : List (Field Head)} (entry : ctors[i]? = some (k, fields))
    {n : Nat} {Γ : CCtx Head n} (σ : CSub Head (1 + ctors.length + fields.length) n)
    (typed : CSubstMor (withInductive B T u ctors rec v) (liftCtx (iotaTele T v ctors fields))
      Γ σ) :
    CEqual (withInductive B T u ctors rec v) Γ
      ((liftTm (iotaLeft rec k ctors.length fields.length)).subst σ)
      ((liftTm (iotaRight rec ctors.length i fields)).subst σ)
      ((liftTm (iotaTarget k ctors.length fields.length)).subst σ) :=
  iota_holds_within levels B (ChurchRulesSub.refl _) (StepsWithin.sum_right _ _) hu hv distinct
    free new fieldsFormed entry σ typed

/-- **The declaration's declared types are those of every package containing it**: its names
are new to the base package, so the sum declares them as the declaration does. -/
theorem inductive_declared_within (sub : ChurchRulesSub (withInductive B T u ctors rec v) Q)
    (new : NewNames B T ctors rec) {c : DeclName} {D : CTm Head 0}
    (declared : elabDeclarations (inductiveDecls T u ctors rec v) c = some D) :
    Q.constantType c = some D := by
  apply sub.constantType
  obtain ⟨type, found, -⟩ := Option.map_eq_some_iff.mp declared
  have fresh : B.constantType c = none := by
    rcases inductiveDecls_cases found with ⟨rfl, -⟩ | ⟨i, fields, entry, -⟩ | ⟨rfl, -⟩
    · exact new.typeNew
    · exact new.ctorsNew _ (List.mem_of_getElem? entry)
    · exact new.recNew
  exact (sumDecls_right fresh).trans declared

/-- The left side of a computation rule is an application, not a reflexivity proof. -/
theorem iotaLeft_ne_refl (rec k : DeclName) (c a : Nat) (t : Tm Head (1 + c + a)) :
    iotaLeft rec k c a ≠ .refl t := by
  rw [iotaLeft_spine, show recSpine (Head := Head) k c a = recPrefix c a ++ [scrutinee k c a]
    from rfl, Normalization.appSpine_concat]
  exact fun h => nomatch h

include levels in
/-- **The computation rules of the recursor preserve typing in every package containing the
declaration**, given the injectivity and no-confusion of that package's type formers: a typed
instance of the left side has its metavariables typed along the rule's telescope (pattern
inversion), so the right side has the motive's type at the constructor applied to its fields
(`iota_typed_metaVars`), which is below the instance's type. -/
theorem iota_preservesIn (sub : ChurchRulesSub (withInductive B T u ctors rec v) Q)
    (hu : R.isUniverse u) (hv : R.isUniverse v) (distinct : DistinctNames T ctors rec)
    (free : FieldsLamFree ctors) (new : NewNames B T ctors rec)
    (fieldsFormed : FieldsFormed B ctors) (facts : CFormerFacts Q) (levelsQ : LevelModel R' L)
    {n : Nat} {Γ : CCtx Head n} {l r A : CTm Head n} (formed : CCtxFormed Q Γ)
    (step : (inductiveChurch R T u ctors rec v).computation.step l r)
    (typing : CTyped Q Γ l A) : CTyped Q Γ r A :=
  ChurchRules.ofSchemas_preservesIn (iotaSchema rec ctors) (iota_presents rec ctors)
    (fun rule => by
      obtain ⟨i, k, fields, entry, same⟩ := rule
      cases same
      refine SchemaPreserving.of_templateTyped facts levelsQ (inductive_declared_within B sub new)
        (firstOrder_iotaLeft rec k _ _) (iotaLeft_ne_refl rec k _ _)
        ⟨liftCtx (iotaTele T v ctors fields), liftTm (iotaTarget k ctors.length fields.length),
          iotaLeft_known distinct free entry, iotaLeft_type (elab_recursor distinct free) k _, ?_⟩
      have right : elabRight (elabDeclarations (inductiveDecls T u ctors rec v))
          (iotaLeft rec k ctors.length fields.length) (iotaRight rec ctors.length i fields) =
          liftTm (iotaRight rec ctors.length i fields) :=
        elab_lamFree _ (lamFree_iotaRight rec _ i fields) _ _ _
      rw [right]
      exact CDerivable.mono sub
        (iota_typed_metaVars levels B hu hv distinct free new fieldsFormed entry).2)
    formed step typing

/-- **The computation rules of the recursor are premised in every package containing the
declaration and its steps**: pattern inversion reads the typings of the motive, the methods and
the fields off the typing of a left side, and they are the step's only premises. -/
theorem iota_premisedIn (sub : ChurchRulesSub (withInductive B T u ctors rec v) Q)
    (steps : StepsWithin (inductiveChurch R T u ctors rec v) Q) (new : NewNames B T ctors rec)
    (facts : CFormerFacts Q) (levelsQ : LevelModel R' L)
    {n : Nat} {Γ : CCtx Head n} {l r A : CTm Head n} (formed : CCtxFormed Q Γ)
    (step : (inductiveChurch R T u ctors rec v).computation.step l r)
    (typing : CTyped Q Γ l A) : Q.Admits Γ l r :=
  ChurchRules.ofSchemas_premisedIn (iotaSchema rec ctors) (iota_presents rec ctors)
    (fun rule => by
      obtain ⟨i, k, fields, entry, same⟩ := rule
      cases same
      exact firstOrder_iotaLeft rec k _ _)
    (inductive_declared_within B sub new)
    (fun required => by
      cases required with
      | instantiate rule σ =>
          exact steps.requires (CSchemaStep.instantiate ⟨_, _, rule, rfl, rfl⟩ σ)
            (.instantiate rule σ))
    facts levelsQ formed step typing

end Within

end ContainingPackages

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
