import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.ByType.Embed

/-!
# Every by-name law holds for every `byType` program

`byType_eq_byName_proj` makes a `byType` run the by-name run of the program's projection. The
study's general by-name theorems (`Laws.byName_laws`, `Nested.four_combinations`) therefore hold for
every typed program of the same shape, with any held parameter type (`Atom` or `(Code T)`) and any
unchecked value result (`Proc`, `%Undefined%`, a type variable):

* identity insertion (`byType_identity`), the fourth law;
* HE's `if` written as a function (`byType_if`);
* the plain reading at a field of an undeclared head (`byType_field`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Core CoreLaws Typed Acceptance

namespace ByType

/-- `byType`'s printed answers are by-name's on the projection, at every fuel. -/
theorem answersB_byType_eq (P : TProg) (n : Nat) (q : Atom) :
    answersB byType P n q = answers byName (projP P) n q := by
  have hprog := byType_eq_byName_proj P
  have hq : queryB byType P q = elabQuery byName (modesOf (projP P)) q :=
    congrFun (congrArg Prog.code hprog) q
  unfold answersB runB answers
  rw [hprog, hq]
  rfl

theorem printsB_byType_iff (P : TProg) (q : Atom) (L : List Atom) :
    PrintsB byType P q L ↔ Laws.Prints byName (projP P) q L := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← answersB_byType_eq]; exact hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [answersB_byType_eq]; exact hn⟩

theorem projTy_held {H : CTy} (h : H.holds = true) : projTy H = .atom := by
  cases H <;> simp_all [CTy.holds, projTy]

theorem unchecked_proj {R : CTy} (h : UncheckedT R) : Laws.Unchecked (projTy R) := by
  rcases h with rfl | rfl | ⟨a, rfl⟩
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

/-! ## Identity insertion -/

/-- `(: myid (-> T T)) (= (myid $x) $x)`, the study's evaluated identity. -/
def valueIdX (T : CTy) : TFn := ⟨"myid", some ([T], T), [([V "x"], V "x")]⟩

/-- `(: g' (-> H R)) (= (g' $x) (myid $x))`. -/
def viaIdT (H R : CTy) : TFn := ⟨"g'", some ([H], R), [([V "x"], E [S "myid", V "x"])]⟩

/-- The program of the identity law, typed. -/
def identityProgT (H R T : CTy) (P0 : TProg) : TProg :=
  heldBodyT "g" H R (V "x") :: viaIdT H R :: valueIdX T :: P0

theorem projP_identity {H : CTy} (hH : H.holds = true) (R T : CTy) (P0 : TProg) :
    projP (identityProgT H R T P0) = Laws.identityProg (projTy R) (projTy T) (projP P0) := by
  simp [projP, identityProgT, Laws.identityProg, projFn, heldBodyT, viaIdT, valueIdX, heldId,
    Laws.viaIdFn, valueId, projTy_held hH]

/-- **Identity insertion in `byType`**, for every typed program. -/
theorem byType_identity {H : CTy} (hH : H.holds = true) {R T : CTy} (hR : UncheckedT R)
    (hT : UncheckedT T) (P0 : TProg) (M : Atom) (L : List Atom) :
    PrintsB byType (identityProgT H R T P0) (Laws.gQ M) L ↔
      PrintsB byType (identityProgT H R T P0) (Laws.g'Q M) L := by
  rw [printsB_byType_iff, printsB_byType_iff, projP_identity hH]
  exact Laws.byName_laws.2.2.2.2.2.1 (projP P0) (projTy R) (projTy T) M L (unchecked_proj hR)
    (unchecked_proj hT)

/-! ## HE's `if` -/

/-- `(: my-if (-> Bool H H R))` with HE's two equations. -/
def myIfT (H R : CTy) : TFn :=
  ⟨"my-if", some ([.bool, H, H], R),
    [([S "True", V "t", V "e"], V "t"), ([S "False", V "t", V "e"], V "e")]⟩

theorem projP_myIf {H : CTy} (hH : H.holds = true) (R : CTy) (P0 : TProg) :
    projP (myIfT H R :: P0) = myIf (projTy R) :: projP P0 := by
  simp [projP, myIfT, myIf, projFn, projTy_held hH, show projTy .bool = .bool from rfl]

/-- **HE's `if` in `byType`**: `(my-if True M N)` prints what `M` prints, for closed `M`, `N`, every
held branch type and every typed program. -/
theorem byType_if {H : CTy} (hH : H.holds = true) {R : CTy} (hR : UncheckedT R) (P0 : TProg)
    (M N : Atom) (hM : Laws.Closed M) (hN : Laws.Closed N) (L : List Atom) :
    PrintsB byType (myIfT H R :: P0) (Laws.ifQ M N) L ↔ PrintsB byType (myIfT H R :: P0) M L := by
  rw [printsB_byType_iff, printsB_byType_iff, projP_myIf hH]
  exact Laws.byName_laws.2.2.2.2.1 (projP P0) (projTy R) M N L (unchecked_proj hR) hM hN

/-! ## The plain reading at a field -/

/-- `(: g (-> H R)) (= (g $x) (wrap $x))`. -/
def wrapFnT (H R : CTy) : TFn := heldBodyT "g" H R (E [S "wrap", V "x"])

theorem projP_wrap {H : CTy} (hH : H.holds = true) (R : CTy) (P0 : TProg) :
    projP (wrapFnT H R :: P0) = Nested.wrapFn (projTy R) :: projP P0 := by
  simp [projP, wrapFnT, heldBodyT, Nested.wrapFn, projFn, projTy_held hH]

/-- **The plain reading at a field in `byType`**: `(g M)` prints what the written `(wrap M)` prints,
for every typed program in which `wrap` has no declaration. -/
theorem byType_field {H : CTy} (hH : H.holds = true) {R : CTy} (hR : UncheckedT R) (P0 : TProg)
    (hw : tmodesOf (wrapFnT H R :: P0) "wrap" 1 = none) (M : Atom) (L : List Atom) :
    PrintsB byType (wrapFnT H R :: P0) (Laws.gQ M) L ↔
      PrintsB byType (wrapFnT H R :: P0) (Nested.wrapQ M) L := by
  rw [printsB_byType_iff, printsB_byType_iff, projP_wrap hH]
  have hw' : modesOf (Nested.wrapFn (projTy R) :: projP P0) "wrap" 1 = none := by
    rw [← projP_wrap hH R P0, modesOf_projP]
    simp [hw]
  exact Nested.four_combinations.1.1 (projP P0) (projTy R) M L (unchecked_proj hR) hw'

end ByType

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes
