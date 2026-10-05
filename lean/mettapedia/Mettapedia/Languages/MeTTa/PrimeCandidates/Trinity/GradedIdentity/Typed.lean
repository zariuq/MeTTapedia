import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectPrograms
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectAdditionInduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ScopedComputationPreservation

/-!
# The shared graded identity, typed

The typed face of the shared graded identity of `Joined.lean`: the weight carriers are
declarations of a package with their laws derived in it, and the specimen is a typed
computation over them.

**The weight package** (`weights`) is the object package with a list of declarations
(`weightProgram`), the head of the list added last:

* `NumberPair`, with `Pair : num → num → NumberPair`: the values the specimen returns;
* `Boolean`, with `True` and `False`: the Boolean weights;
* `Evidence`, with `evidence : num → num → Evidence`: evidence counts;
* `mul : num → num → num`, the product of numbers, by the recursor of the numbers on its
  second argument, so that `mul a 0 ≡ 0` and `mul a (suc b) ≡ add (mul a b) a`
  (`wMulZero`, `wMulSuc`);
* `positive` and `negative : Evidence → num`, the two counts of a packet, by recursion;
* `evidence-eta : Π (e : Evidence). Id Evidence (evidence (positive e) (negative e)) e`, a
  proof by induction written as a definition by recursion;
* `tensor : Evidence → Evidence → Evidence`, the product of packets count by count;
* `number-weight : num → num`, `x ↦ x`, and `count-weight : num → Evidence`,
  `n ↦ evidence n 1`: the value-to-weight maps of `weigh-by-self` on the two carriers, typed
  constants (`numberWeight_typed`, `countWeight_typed`) that compute by their equations
  (`numberWeight_rule`, `countWeight_rule`).

The list is admissible (`weightProgram_admissible`). By the criterion for admissible lists over
the object package the package has a set model and is consistent, relative to
`CofinalInaccessibles` (`weights_model`, `weights_consistent`).

**The monoid laws are derived in the package**, as closed terms of identity types. None is
declared, and none uses commutativity.

* Numbers: `mul_assoc_identity`, `mul_one_left_identity` (both by induction) and
  `mul_one_right_identity`, through `add_assoc_identity` and `mul_add_identity` (the product
  distributes over a sum on its right).
* Evidence counts, with the unit `evidence 1 1`: `tensor_assoc_identity`,
  `tensor_one_left_identity`, `tensor_one_right_identity`, from the laws of numbers and
  `evidence-eta`.

In the model the laws hold of the values (`mul_assoc_value`, `tensor_assoc_value`).

Negative example: `number-weight` does not have the type `num → Boolean`
(`numberWeight_not_boolean`). A number used as a Boolean weight is ill-typed: in the model zero
is the empty set and every Boolean is a constructor value, which is never empty.

**The typed computation.** Over the rules of the package read without annotations
(`weightRules`), the specimen is a scoped computation whose one operation charges a stored row
with a weight of the carrier and returns that weight (`gradeSignature`). A stored row charges
its grade and returns its value (`storedRow`). The graded identity charges the weight of its
argument, computed by the carrier's typed map, and returns the argument (`gradedIdentity`). The
coin is a choice over its three stored rows (`coinCode`), and
`(paired (weigh-by-self (coin)))` sequences the producer once and uses its one selected value
twice (`sharedPairCode`). Its typing derivation (`sharedPair_typing`, on both carriers) binds
the selected value once and types the identity's charge and the pair in its scope; the type of
the result, `NumberPair`, does not itself depend on that value.
`(weigh-by-self (weigh-by-self 7))` is typed by `nested_typing`, and the identity over a coin with an
ungraded row by `coinThroughId_typing`.

The charge primitive (`chargeWorlds`) is realized by its contextual handler
(`chargeHandler_realizes`), and its result contract holds for every admitted grade
(`charge_preserves`). Result preservation at the specimen follows from the general theorem
(`sharedPair_results`, `nested_results`, `sharedPair_world_results`).

Grade terms are read as numbers and as evidence counts (`readNumber`, `readCount`). A term read
as `k` is typed as a number and equal in the judgment to the numeral `k` (`readNumber_sound`),
and a term read as the counts `(a, b)` is equal to `evidence a b` (`readCount_sound`): the
reading of `number-weight 2` as `2` is the equation of the declared map. Positive examples: the
coefficient `3 * number-weight 2` of an occurrence of the shared pair is `6` in the package
(`coefficient_six`), and `tensor (evidence 3 1) (count-weight 2)` is `evidence 6 1`
(`packet_six`).

**A zero-rejecting guard** (`guardedWorlds`): a charge whose grade is zero produces no world.
It keeps the result contract (`guarded_preserves`), so the direct worlds of a guarded program
have typed results (`coinThroughId_guarded_results`). No contextual handler realizes it: those
always produce a world (`guarded_no_handler`).

Negative example: a fresh producer at each use of `paired` (`freshPairCode`) is typed as well
(`freshPair_typing`), so the typing alone does not tell the two programs apart. Their
occurrences do; `Joined.lean` compares both with the annotated occurrences.

Not here: a typing of every term of the graded fragment, a typed account of the native
machine's intermediate states, and a refutation of ill-typed raw terms in the
formation-sensitive judgment (the Boolean control is stated in the annotated judgment, through
its set model).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.GradedIdentity.Typed

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram
open ExecutableModel ExecutableModel.CodeModel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.TypedEquality Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated

/-! ## The names and the declarations -/

/-- The type of the pairs of numbers. -/
def numberPairN : DeclName := .str .anonymous "NumberPair"
/-- The pair of two numbers. -/
def pairCtorN : DeclName := .str .anonymous "Pair"
/-- The recursor of the pairs of numbers. -/
def numberPairRecN : DeclName := .str .anonymous "NumberPair-rec"
/-- The type of the Boolean weights. -/
def booleanN : DeclName := .str .anonymous "Boolean"
/-- The Boolean `True`. -/
def trueN : DeclName := .str .anonymous "True"
/-- The Boolean `False`. -/
def falseN : DeclName := .str .anonymous "False"
/-- The recursor of the Booleans. -/
def booleanRecN : DeclName := .str .anonymous "Boolean-rec"
/-- The type of evidence counts. -/
def evidenceTypeN : DeclName := .str .anonymous "Evidence"
/-- The packet of a positive and a negative count. -/
def evidenceN : DeclName := .str .anonymous "evidence"
/-- The recursor of evidence counts. -/
def evidenceRecN : DeclName := .str .anonymous "Evidence-rec"
/-- The product of two numbers. -/
def mulN : DeclName := .str .anonymous "mul"
/-- The positive count of a packet. -/
def positiveN : DeclName := .str .anonymous "positive"
/-- The negative count of a packet. -/
def negativeN : DeclName := .str .anonymous "negative"
/-- Every packet is the packet of its two counts. -/
def evidenceEtaN : DeclName := .str .anonymous "evidence-eta"
/-- The product of two packets. -/
def tensorN : DeclName := .str .anonymous "tensor"
/-- The weight of a number read as a number. -/
def numberWeightN : DeclName := .str .anonymous "number-weight"
/-- The weight of a number read as an evidence count. -/
def countWeightN : DeclName := .str .anonymous "count-weight"

section Terms

variable {n : Nat}

abbrev cNumberPair : CTm Tower.Head n := .const numberPairN
abbrev cPair (a b : CTm Tower.Head n) : CTm Tower.Head n := .app (.app (.const pairCtorN) a) b
abbrev cBoolean : CTm Tower.Head n := .const booleanN
abbrev cEvidence : CTm Tower.Head n := .const evidenceTypeN
abbrev cevidence (p q : CTm Tower.Head n) : CTm Tower.Head n := .app (.app (.const evidenceN) p) q
abbrev cmul (a b : CTm Tower.Head n) : CTm Tower.Head n := .app (.app (.const mulN) a) b
abbrev cpositive (e : CTm Tower.Head n) : CTm Tower.Head n := .app (.const positiveN) e
abbrev cnegative (e : CTm Tower.Head n) : CTm Tower.Head n := .app (.const negativeN) e
abbrev ctensor (e f : CTm Tower.Head n) : CTm Tower.Head n := .app (.app (.const tensorN) e) f
abbrev cone : CTm Tower.Head n := csuc czero
abbrev cunit : CTm Tower.Head n := cevidence cone cone

/-- The motive of the recursion that defines the product: every number gives a number. -/
abbrev mulMotive : CTm Tower.Head n := .lam cnum cnum

/-- The inner step of the product by `a`, over the number reached: from the product at it,
that product plus `a`. -/
abbrev mulInner (a : CTm Tower.Head (n + 1)) : CTm Tower.Head (n + 1) :=
  .lam (.app mulMotive (.var 0)) (cadd (.var 0) (a.rename wk))

/-- The step of the product by `a`: from a number and the product at it, that product plus
`a`. -/
abbrev mulStep (a : CTm Tower.Head n) : CTm Tower.Head n := .lam cnum (mulInner (a.rename wk))

end Terms

/-- The constructor of the pairs of numbers. -/
def pairCtors : List (DeclName × List CtorField) :=
  [(pairCtorN, [.closed (.const numN), .closed (.const numN)])]

/-- The constructors of the Booleans. -/
def booleanCtors : List (DeclName × List CtorField) := [(trueN, []), (falseN, [])]

/-- The constructor of evidence counts. -/
def evidenceCtors : List (DeclName × List CtorField) :=
  [(evidenceN, [.closed (.const numN), .closed (.const numN)])]

/-- **The pairs of numbers**, `Pair : num → num → NumberPair`. -/
def pairDecl : Datatype Tower.Head where
  type := numberPairN
  typeUniverse := .sort Tower.zero
  ctors := pairCtors
  recursor := numberPairRecN
  motiveUniverse := listMotives

/-- **The Booleans**, `True` and `False`. -/
def booleanDecl : Datatype Tower.Head where
  type := booleanN
  typeUniverse := .sort Tower.zero
  ctors := booleanCtors
  recursor := booleanRecN
  motiveUniverse := listMotives

/-- **Evidence counts**, `evidence : num → num → Evidence`. -/
def evidenceDecl : Datatype Tower.Head where
  type := evidenceTypeN
  typeUniverse := .sort Tower.zero
  ctors := evidenceCtors
  recursor := evidenceRecN
  motiveUniverse := listMotives

/-- **The product**, an explicit definition by the recursor of the numbers on its second
argument: `mul a b ⟶ num-rec (λ _. num) zero (λ k r. add r a) b`. -/
def mulDef : ExplicitDefinition Tower.Head where
  name := mulN
  width := 2
  arguments := .cons cnum (.cons cnum .nil)
  result := cnum
  body := (cRecApp mulMotive czero (mulStep (.var 1)) (.var 0) : CTm Tower.Head 2)

/-- The right side of a projection of a packet: the field it keeps. -/
def projectionBody (keep : Fin 2) : (k : DeclName) → (fields : List CtorField) →
    CTm Tower.Head
      ((CTele.nil : CTele Tower.Head 1 1).endAt (fields.length + (recPositions fields).length))
  | _, [.closed _, .closed _] => (.var keep : CTm Tower.Head 2)
  | _, _ => .const .anonymous

/-- **The positive count**, `positive (evidence p q) ⟶ p`. -/
def positiveDef : RecursiveDefinition Tower.Head where
  name := positiveN
  datatype := evidenceDecl
  width := 1
  later := .nil
  result := cnum
  body := projectionBody 1

/-- **The negative count**, `negative (evidence p q) ⟶ q`. -/
def negativeDef : RecursiveDefinition Tower.Head where
  name := negativeN
  datatype := evidenceDecl
  width := 1
  later := .nil
  result := cnum
  body := projectionBody 0

/-- The statement at a packet: the packet of its two counts is the packet. -/
abbrev etaAt {n : Nat} (e : CTm Tower.Head n) : CTm Tower.Head n :=
  .id cEvidence (cevidence (cpositive e) (cnegative e)) e

/-- The right side of the proof: reflexivity at the packet of the two fields. -/
def etaBody : (k : DeclName) → (fields : List CtorField) →
    CTm Tower.Head
      ((CTele.nil : CTele Tower.Head 1 1).endAt (fields.length + (recPositions fields).length))
  | _, [.closed _, .closed _] => (.refl (cevidence (.var 1) (.var 0)) : CTm Tower.Head 2)
  | _, _ => .const .anonymous

/-- **Every packet is the packet of its counts**, a proof by induction as a definition by
recursion: `evidence-eta (evidence p q) ⟶ refl (evidence p q)`. -/
def evidenceEtaDef : RecursiveDefinition Tower.Head where
  name := evidenceEtaN
  datatype := evidenceDecl
  width := 1
  later := .nil
  result := etaAt (.var 0)
  body := etaBody

/-- **The product of packets**, count by count:
`tensor e f ⟶ evidence (mul (positive e) (positive f)) (mul (negative e) (negative f))`. -/
def tensorDef : ExplicitDefinition Tower.Head where
  name := tensorN
  width := 2
  arguments := .cons cEvidence (.cons cEvidence .nil)
  result := cEvidence
  body := (cevidence (cmul (cpositive (.var 1)) (cpositive (.var 0)))
    (cmul (cnegative (.var 1)) (cnegative (.var 0))) : CTm Tower.Head 2)

/-- **The weight of a number read as a number**: `number-weight x ⟶ x`. -/
def numberWeightDef : ExplicitDefinition Tower.Head where
  name := numberWeightN
  width := 1
  arguments := .cons cnum .nil
  result := cnum
  body := (.var 0 : CTm Tower.Head 1)

/-- **The weight of a number read as an evidence count**: `count-weight n ⟶ evidence n 1`. -/
def countWeightDef : ExplicitDefinition Tower.Head where
  name := countWeightN
  width := 1
  arguments := .cons cnum .nil
  result := cEvidence
  body := (cevidence (.var 0) cone : CTm Tower.Head 1)

/-! ## The stages of the package -/

abbrev stage1 : List (Declaration Tower.Head) := [.datatype pairDecl]
abbrev stage2 : List (Declaration Tower.Head) := .datatype booleanDecl :: stage1
abbrev stage3 : List (Declaration Tower.Head) := .datatype evidenceDecl :: stage2
abbrev stage4 : List (Declaration Tower.Head) := .definition (.explicit mulDef) :: stage3
abbrev stage5 : List (Declaration Tower.Head) := .definition (.recursive positiveDef) :: stage4
abbrev stage6 : List (Declaration Tower.Head) := .definition (.recursive negativeDef) :: stage5
abbrev stage7 : List (Declaration Tower.Head) := .definition (.recursive evidenceEtaDef) :: stage6
abbrev stage8 : List (Declaration Tower.Head) := .definition (.explicit tensorDef) :: stage7
abbrev stage9 : List (Declaration Tower.Head) :=
  .definition (.explicit numberWeightDef) :: stage8

/-- **The weight program**: the pairs of numbers, the Booleans, evidence counts, the product
of numbers, the two counts of a packet, the proof that a packet is the packet of its counts,
the product of packets, and the two value-to-weight maps. The head of the list is the
declaration added last. -/
abbrev weightProgram : List (Declaration Tower.Head) :=
  .definition (.explicit countWeightDef) :: stage9

/-- **The weight package**: the object package with the weight program. -/
abbrev weights := withDeclarations objectChurch weightProgram

/-! ## Typing in every package over the object package -/

section Toolkit

variable {R' : Rules Tower.Head} {P : ChurchRules R'} (sub : ChurchRulesSub objectChurch P)
  {n : Nat} {Γ : CCtx Tower.Head n}

include sub

theorem tNum : CTyped P Γ cnum cU0 := cnum_typed.mono sub
theorem tZero : CTyped P Γ czero cnum := czero_typed.mono sub
theorem tSuc {a : CTm Tower.Head n} (ha : CTyped P Γ a cnum) : CTyped P Γ (csuc a) cnum :=
  .appElim (B := cnum) (csucConst_typed.mono sub) ha
theorem tAdd {a b : CTm Tower.Head n} (ha : CTyped P Γ a cnum) (hb : CTyped P Γ b cnum) :
    CTyped P Γ (cadd a b) cnum :=
  .appElim (B := cnum) (.appElim (B := .pi cnum cnum) (caddConst_typed.mono sub) ha) hb
theorem tOne : CTyped P Γ cone cnum := tSuc sub (tZero sub)

theorem uSort (l : LevelExpr Nat) : R'.isUniverse (.sort l) := sub.isUniverse (.sort l)

theorem tPi {D : CTm Tower.Head n} {B : CTm Tower.Head (n + 1)} {l : LevelExpr Nat}
    (domain : CTyped P Γ D (CU l)) (codomain : CTyped P (.snoc Γ D) B (CU l)) :
    CTyped P Γ (.pi D B) (CU l) :=
  CDerivable.cumul (.piForm domain (uSort sub l) codomain (uSort sub l) (sub.join (.sorts l l)))
    (sub.cumulative fun valuation => by simp [LevelExpr.eval])

theorem tId {C a b : CTm Tower.Head n} {l : LevelExpr Nat} (carrier : CTyped P Γ C (CU l))
    (left : CTyped P Γ a C) (right : CTyped P Γ b C) : CTyped P Γ (.id C a b) (CU l) :=
  .idForm carrier (uSort sub l) left right

theorem tRaise {T : CTm Tower.Head n} (typed : CTyped P Γ T cU0) : CTyped P Γ T cU1 :=
  CDerivable.cumul typed (sub.cumulative fun valuation => by simp [LevelExpr.eval, LevelTower.zero])

theorem tU0 : CTyped P Γ cU0 cU1 := cU0_typed.mono sub

/-- **Congruence of identity proofs** in every package over the object package. -/
theorem tCong {A B f x y p : CTm Tower.Head n}
    (hA : CTyped P Γ A cU0) (hB : CTyped P Γ B cU0)
    (hf : CTyped P Γ f (.pi A (B.rename wk))) (hx : CTyped P Γ x A)
    (hy : CTyped P Γ y A) (hp : CTyped P Γ p (.id A x y)) :
    CTyped P Γ (congOf A B f x y p) (.id B (.app f x) (.app f y)) :=
  CTyped.substitute (congTerm_typed.mono sub) (σ := fun i => [p, y, x, f, B, A].getD i.val A)
    (fun j => match j with
      | ⟨0, _⟩ => hp
      | ⟨1, _⟩ => hy
      | ⟨2, _⟩ => hx
      | ⟨3, _⟩ => hf
      | ⟨4, _⟩ => hB
      | ⟨5, _⟩ => hA)

/-- **Symmetry of identity proofs** in every package over the object package. -/
theorem tSym {A x y p : CTm Tower.Head n} (hA : CTyped P Γ A cU0) (hx : CTyped P Γ x A)
    (hy : CTyped P Γ y A) (hp : CTyped P Γ p (.id A x y)) :
    CTyped P Γ (symOf A x y p) (.id A y x) :=
  CTyped.substitute (symTerm_typed.mono sub) (σ := fun i => [p, y, x, A].getD i.val A)
    (fun j => match j with
      | ⟨0, _⟩ => hp
      | ⟨1, _⟩ => hy
      | ⟨2, _⟩ => hx
      | ⟨3, _⟩ => hA)

/-- **Transitivity of identity proofs** in every package over the object package. -/
theorem tTrans {A x y z p q : CTm Tower.Head n} (hA : CTyped P Γ A cU0)
    (hx : CTyped P Γ x A) (hy : CTyped P Γ y A) (hz : CTyped P Γ z A)
    (hp : CTyped P Γ p (.id A x y)) (hq : CTyped P Γ q (.id A y z)) :
    CTyped P Γ (transOf A x y z p q) (.id A x z) :=
  CTyped.substitute (transTerm_typed.mono sub) (σ := fun i => [q, p, z, y, x, A].getD i.val A)
    (fun j => match j with
      | ⟨0, _⟩ => hq
      | ⟨1, _⟩ => hp
      | ⟨2, _⟩ => hz
      | ⟨3, _⟩ => hy
      | ⟨4, _⟩ => hx
      | ⟨5, _⟩ => hA)

/-- **The typing rule of the recursor of the numbers** in every package over the object
package. -/
theorem tRec {M z s q : CTm Tower.Head n}
    (hM : CTyped P Γ M (.pi cnum cU0)) (hz : CTyped P Γ z (.app M czero))
    (hs : CTyped P Γ s
      (.pi cnum (.pi (.app (M.rename wk) (.var 0))
        (.app ((M.rename wk).rename wk) (csuc (.var 1))))))
    (hq : CTyped P Γ q cnum) : CTyped P Γ (cRecApp M z s q) (.app M q) :=
  CTyped.substitute (cRecSpine_typed.mono sub) (σ := fun i => [q, s, z, M].getD i.val M)
    (fun j => match j with
      | ⟨0, _⟩ => hq
      | ⟨1, _⟩ => hs
      | ⟨2, _⟩ => hz
      | ⟨3, _⟩ => hM)

/-- Addition with zero on the right computes, in every package over the object package. -/
theorem eAddZero {a : CTm Tower.Head n} (ha : CTyped P Γ a cnum) :
    CEqual P Γ (cadd a czero) a cnum :=
  CEqual.substitute ((cadd_zero (Γ := .snoc .nil cnum) (.var 0)).mono sub)
    (σ := fun _ => a) (fun j => match j with | ⟨0, _⟩ => ha)

/-- Addition with a successor on the right computes, in every package over the object
package. -/
theorem eAddSuc {a b : CTm Tower.Head n} (ha : CTyped P Γ a cnum) (hb : CTyped P Γ b cnum) :
    CEqual P Γ (cadd a (csuc b)) (csuc (cadd a b)) cnum :=
  CEqual.substitute ((cadd_suc (Γ := .snoc (.snoc .nil cnum) cnum) (.var 1) (.var 0)).mono sub)
    (σ := fun i => [b, a].getD i.val a)
    (fun j => match j with
      | ⟨0, _⟩ => hb
      | ⟨1, _⟩ => ha)

/-- The successor is a congruence of the judgment's equality. -/
theorem eSuc {a b : CTm Tower.Head n} (equal : CEqual P Γ a b cnum) :
    CEqual P Γ (csuc a) (csuc b) cnum :=
  .appCong (B := cnum) (.refl (csucConst_typed.mono sub)) equal

/-- Addition is a congruence of the judgment's equality. -/
theorem eAdd {a a' b b' : CTm Tower.Head n} (ea : CEqual P Γ a a' cnum)
    (eb : CEqual P Γ b b' cnum) : CEqual P Γ (cadd a b) (cadd a' b') cnum :=
  .appCong (B := cnum) (.appCong (B := .pi cnum cnum) (.refl (caddConst_typed.mono sub)) ea) eb

end Toolkit


/-! ## The product of numbers, in the object package -/

section MulBody

variable {n : Nat} {Γ : CCtx Tower.Head n}

theorem mulMotive_typed : CTyped objectChurch Γ mulMotive (.pi cnum cU0) :=
  .lamIntro cnum_typed (.sort _) (cpiT (craise cnum_typed) cU0_typed) (.sort _) cnum_typed

/-- The motive at a number is the numbers. -/
theorem mulMotive_at {t : CTm Tower.Head n} (ht : CTyped objectChurch Γ t cnum) :
    CEqual objectChurch Γ (.app mulMotive t) cnum cU0 :=
  .betaPi (A := cnum) (B := cU0) (body := cnum) (a := t)
    (cpiT (craise cnum_typed) cU0_typed) (.sort _) cnum_typed ht

/-- The type of the inner step, over the number reached. -/
theorem mulInnerPi_typed :
    CTyped objectChurch (.snoc Γ cnum) (.pi (.app mulMotive (.var 0)) (.app mulMotive (csuc
        (.var 1))))
      cU0 :=
  cpiT (.appElim (B := cU0) mulMotive_typed (.var 0))
    (.appElim (B := cU0) mulMotive_typed (csuc_typed (.var 1)))

theorem mulInnerBody_typed {a : CTm Tower.Head (n + 1)}
    (ha : CTyped objectChurch (.snoc Γ cnum) a cnum) :
    CTyped objectChurch (.snoc (.snoc Γ cnum) (.app mulMotive (.var 0)))
      (cadd (.var 0) (a.rename wk)) (.app mulMotive (csuc (.var 1))) :=
  .conv (cadd_typed (.conv (.var 0) (mulMotive_at (.var 1)) (.sort _)) (CTyped.weaken ha))
    (.symm (mulMotive_at (csuc_typed (.var 1)))) (.sort _)

theorem mulInner_typed {a : CTm Tower.Head (n + 1)}
    (ha : CTyped objectChurch (.snoc Γ cnum) a cnum) :
    CTyped objectChurch (.snoc Γ cnum) (mulInner a)
      (.pi (.app mulMotive (.var 0)) (.app mulMotive (csuc (.var 1)))) :=
  .lamIntro (.appElim (B := cU0) mulMotive_typed (.var 0)) (.sort _) mulInnerPi_typed (.sort _)
    (mulInnerBody_typed ha)

theorem mulStep_typed {a : CTm Tower.Head n} (ha : CTyped objectChurch Γ a cnum) :
    CTyped objectChurch Γ (mulStep a)
      (.pi cnum (.pi (.app mulMotive (.var 0)) (.app mulMotive (csuc (.var 1))))) :=
  .lamIntro cnum_typed (.sort _) (cpiT cnum_typed mulInnerPi_typed) (.sort _)
    (mulInner_typed (CTyped.weaken ha))

/-- The right side of the product is a number, over two numbers. -/
theorem mulBody_typed : CTyped objectChurch (.snoc (.snoc .nil cnum) cnum)
    (cRecApp mulMotive czero (mulStep (.var 1)) (.var 0)) cnum :=
  .conv (numRec_typed mulMotive_typed (.conv czero_typed (.symm (mulMotive_at czero_typed))
      (.sort _))
    (mulStep_typed (.var 1)) (.var 0)) (mulMotive_at (.var 0)) (.sort _)

end MulBody

/-! ## The program is admissible -/

/-- A constructor with two numbers as fields has no abstraction in its fields. -/
theorem twoNumbers_lamFree (k : DeclName) :
    FieldsLamFree ([(k, [.closed (.const numN), .closed (.const numN)])] :
      List (DeclName × List CtorField)) := by
  intro entry member F field
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at field
  rcases field with same | same
  · obtain rfl : F = .const numN := by injection same
    rfl
  · obtain rfl : F = .const numN := by injection same
    rfl

/-- The fields of a constructor with two numbers are types of the lowest universe. -/
theorem twoNumbers_fields {R' : Rules Tower.Head} {B : ChurchRules R'}
    (sub : ChurchRulesSub objectChurch B) (k : DeclName) :
    ∀ entry ∈ ([(k, [.closed (.const numN), .closed (.const numN)])] :
        List (DeclName × List CtorField)), ∀ F, (.closed F : CtorField) ∈ entry.2 →
      CTyped B .nil (liftTm F) (.head (.sort Tower.zero)) := by
  intro entry member F field
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at field
  rcases field with same | same
  · obtain rfl : F = .const numN := by injection same
    exact tNum sub
  · obtain rfl : F = .const numN := by injection same
    exact tNum sub

theorem pairDecl_admissible : pairDecl.Admissible objectChurch where
  typeUniverse := LevelTower.IsUniverse.sort _
  motiveUniverse := LevelTower.IsUniverse.sort _
  distinct := ⟨by decide, by decide, by decide, by decide⟩
  new := ⟨by decide, by decide, by decide⟩
  lamFree := twoNumbers_lamFree pairCtorN
  fields := twoNumbers_fields (ChurchRulesSub.refl _) pairCtorN

theorem stage1_admissible : AdmissibleDeclarations objectChurch stage1 :=
  ⟨trivial, pairDecl_admissible⟩

theorem booleanDecl_admissible :
    booleanDecl.Admissible (withDeclarations objectChurch stage1) where
  typeUniverse := LevelTower.IsUniverse.sort _
  motiveUniverse := LevelTower.IsUniverse.sort _
  distinct := ⟨by decide, by decide, by decide, by decide⟩
  new := ⟨by decide, by decide, by decide⟩
  lamFree := by
    intro entry member F field
    simp only [booleanDecl, booleanCtors, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact nomatch field
  fields := by
    intro entry member F field
    simp only [booleanDecl, booleanCtors, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact nomatch field

theorem stage2_admissible : AdmissibleDeclarations objectChurch stage2 :=
  ⟨stage1_admissible, booleanDecl_admissible⟩

theorem evidenceDecl_admissible :
    evidenceDecl.Admissible (withDeclarations objectChurch stage2) where
  typeUniverse := LevelTower.IsUniverse.sort _
  motiveUniverse := LevelTower.IsUniverse.sort _
  distinct := ⟨by decide, by decide, by decide, by decide⟩
  new := ⟨by decide, by decide, by decide⟩
  lamFree := twoNumbers_lamFree evidenceN
  fields := twoNumbers_fields (withDeclarations_base objectChurch stage2) evidenceN

theorem stage3_admissible : AdmissibleDeclarations objectChurch stage3 :=
  ⟨stage2_admissible, evidenceDecl_admissible⟩

theorem mulDef_admissible : mulDef.Admissible (withDeclarations objectChurch stage3) where
  new := by decide
  formed :=
    .snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, tNum (withDeclarations_base _ stage3)⟩)
      ⟨_, LevelTower.IsUniverse.sort _, tNum (withDeclarations_base _ stage3)⟩
  resultType := ⟨_, LevelTower.IsUniverse.sort _, tNum (withDeclarations_base _ stage3)⟩
  body := mulBody_typed.mono (withDeclarations_base _ stage3)

theorem stage4_admissible : AdmissibleDeclarations objectChurch stage4 :=
  ⟨stage3_admissible, mulDef_admissible⟩


/-! ## The written equations -/

/-- `mul a b ⟶ num-rec (λ _. num) zero (λ k r. add r a) b`. -/
def mulEquation : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil cnum) cnum
  left := cmul (.var 1) (.var 0)
  right := cRecApp mulMotive czero (mulStep (.var 1)) (.var 0)

/-- `positive (evidence p q) ⟶ p`. -/
def positiveEquation : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil cnum) cnum
  left := cpositive (cevidence (.var 1) (.var 0))
  right := .var 1

/-- `negative (evidence p q) ⟶ q`. -/
def negativeEquation : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil cnum) cnum
  left := cnegative (cevidence (.var 1) (.var 0))
  right := .var 0

/-- `tensor e f ⟶ evidence (mul (positive e) (positive f)) (mul (negative e) (negative f))`. -/
def tensorEquation : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil cEvidence) cEvidence
  left := ctensor (.var 1) (.var 0)
  right := cevidence (cmul (cpositive (.var 1)) (cpositive (.var 0)))
    (cmul (cnegative (.var 1)) (cnegative (.var 0)))

/-- `number-weight x ⟶ x`. -/
def numberWeightEquation : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cnum
  left := .app (.const numberWeightN) (.var 0)
  right := .var 0

/-- `count-weight n ⟶ evidence n 1`. -/
def countWeightEquation : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cnum
  left := .app (.const countWeightN) (.var 0)
  right := cevidence (.var 0) cone

theorem mulDef_equations : mulDef.equations = [mulEquation] := rfl
theorem positiveDef_equations : positiveDef.equations = [positiveEquation] := rfl
theorem negativeDef_equations : negativeDef.equations = [negativeEquation] := rfl
theorem tensorDef_equations : tensorDef.equations = [tensorEquation] := rfl
theorem numberWeightDef_equations : numberWeightDef.equations = [numberWeightEquation] := rfl
theorem countWeightDef_equations : countWeightDef.equations = [countWeightEquation] := rfl

/-! ## The declared constants are typed where they are declared -/

section Declared

variable {ds : List (Declaration Tower.Head)} (adm : AdmissibleDeclarations objectChurch ds)
  {n : Nat} {Γ : CCtx Tower.Head n}

include adm

theorem tEvidenceType (member : Declaration.datatype evidenceDecl ∈ ds) :
    CTyped (withDeclarations objectChurch ds) Γ cEvidence cU0 :=
  adm.type_typed ConvRules.objectLevels member

theorem tNumberPairType (member : Declaration.datatype pairDecl ∈ ds) :
    CTyped (withDeclarations objectChurch ds) Γ cNumberPair cU0 :=
  adm.type_typed ConvRules.objectLevels member

theorem tBooleanType (member : Declaration.datatype booleanDecl ∈ ds) :
    CTyped (withDeclarations objectChurch ds) Γ cBoolean cU0 :=
  adm.type_typed ConvRules.objectLevels member

theorem tEvidenceCtor (member : Declaration.datatype evidenceDecl ∈ ds) :
    CTyped (withDeclarations objectChurch ds) Γ (.const evidenceN) (.pi cnum (.pi cnum
        cEvidence)) :=
  adm.ctor_typed ConvRules.objectLevels (d := evidenceDecl) member (i := 0) rfl

theorem tEvidence (member : Declaration.datatype evidenceDecl ∈ ds) {p q : CTm Tower.Head n}
    (hp : CTyped (withDeclarations objectChurch ds) Γ p cnum)
    (hq : CTyped (withDeclarations objectChurch ds) Γ q cnum) :
    CTyped (withDeclarations objectChurch ds) Γ (cevidence p q) cEvidence :=
  .appElim (B := cEvidence) (.appElim (B := .pi cnum cEvidence) (tEvidenceCtor adm member) hp) hq

theorem tPairCtor (member : Declaration.datatype pairDecl ∈ ds) :
    CTyped (withDeclarations objectChurch ds) Γ (.const pairCtorN)
      (.pi cnum (.pi cnum cNumberPair)) :=
  adm.ctor_typed ConvRules.objectLevels (d := pairDecl) member (i := 0) rfl

theorem tPair (member : Declaration.datatype pairDecl ∈ ds) {a b : CTm Tower.Head n}
    (ha : CTyped (withDeclarations objectChurch ds) Γ a cnum)
    (hb : CTyped (withDeclarations objectChurch ds) Γ b cnum) :
    CTyped (withDeclarations objectChurch ds) Γ (cPair a b) cNumberPair :=
  .appElim (B := cNumberPair) (.appElim (B := .pi cnum cNumberPair) (tPairCtor adm member) ha) hb

theorem tMul (member : Declaration.definition (.explicit mulDef) ∈ ds) {a b : CTm Tower.Head n}
    (ha : CTyped (withDeclarations objectChurch ds) Γ a cnum)
    (hb : CTyped (withDeclarations objectChurch ds) Γ b cnum) :
    CTyped (withDeclarations objectChurch ds) Γ (cmul a b) cnum :=
  .appElim (B := cnum) (.appElim (B := .pi cnum cnum)
    (adm.definition_typed ConvRules.objectLevels (D := .explicit mulDef) member) ha) hb

theorem tPositive (member : Declaration.definition (.recursive positiveDef) ∈ ds)
    {e : CTm Tower.Head n} (he : CTyped (withDeclarations objectChurch ds) Γ e cEvidence) :
    CTyped (withDeclarations objectChurch ds) Γ (cpositive e) cnum :=
  .appElim (B := cnum)
    (adm.definition_typed ConvRules.objectLevels (D := .recursive positiveDef) member) he

theorem tNegative (member : Declaration.definition (.recursive negativeDef) ∈ ds)
    {e : CTm Tower.Head n} (he : CTyped (withDeclarations objectChurch ds) Γ e cEvidence) :
    CTyped (withDeclarations objectChurch ds) Γ (cnegative e) cnum :=
  .appElim (B := cnum)
    (adm.definition_typed ConvRules.objectLevels (D := .recursive negativeDef) member) he

theorem tTensor (member : Declaration.definition (.explicit tensorDef) ∈ ds)
    {e f : CTm Tower.Head n} (he : CTyped (withDeclarations objectChurch ds) Γ e cEvidence)
    (hf : CTyped (withDeclarations objectChurch ds) Γ f cEvidence) :
    CTyped (withDeclarations objectChurch ds) Γ (ctensor e f) cEvidence :=
  .appElim (B := cEvidence) (.appElim (B := .pi cEvidence cEvidence)
    (adm.definition_typed ConvRules.objectLevels (D := .explicit tensorDef) member) he) hf

/-- The evidence constructor is a congruence of the judgment's equality. -/
theorem eEvidence (member : Declaration.datatype evidenceDecl ∈ ds) {p p' q q' : CTm Tower.Head n}
    (ep : CEqual (withDeclarations objectChurch ds) Γ p p' cnum)
    (eq : CEqual (withDeclarations objectChurch ds) Γ q q' cnum) :
    CEqual (withDeclarations objectChurch ds) Γ (cevidence p q) (cevidence p' q') cEvidence :=
  .appCong (B := cEvidence) (.appCong (B := .pi cnum cEvidence) (.refl (tEvidenceCtor adm member))
      ep) eq

/-- `positive (evidence p q) ≡ p`. -/
theorem ePositive (member : Declaration.definition (.recursive positiveDef) ∈ ds)
    (memberEv : Declaration.datatype evidenceDecl ∈ ds) {p q : CTm Tower.Head n}
    (hp : CTyped (withDeclarations objectChurch ds) Γ p cnum)
    (hq : CTyped (withDeclarations objectChurch ds) Γ q cnum) :
    CEqual (withDeclarations objectChurch ds) Γ (cpositive (cevidence p q)) p cnum :=
  definition_equation_holds (D := .recursive positiveDef) member (e := positiveEquation)
    (by rw [show Definition.equations (.recursive positiveDef) = positiveDef.equations from rfl,
      positiveDef_equations]; exact List.mem_singleton_self _)
    (fun i => [q, p].getD i.val p)
    (fun j => match j with
      | ⟨0, _⟩ => hq
      | ⟨1, _⟩ => hp)
    (tPositive adm member (tEvidence adm memberEv hp hq)) hp

/-- `negative (evidence p q) ≡ q`. -/
theorem eNegative (member : Declaration.definition (.recursive negativeDef) ∈ ds)
    (memberEv : Declaration.datatype evidenceDecl ∈ ds) {p q : CTm Tower.Head n}
    (hp : CTyped (withDeclarations objectChurch ds) Γ p cnum)
    (hq : CTyped (withDeclarations objectChurch ds) Γ q cnum) :
    CEqual (withDeclarations objectChurch ds) Γ (cnegative (cevidence p q)) q cnum :=
  definition_equation_holds (D := .recursive negativeDef) member (e := negativeEquation)
    (by rw [show Definition.equations (.recursive negativeDef) = negativeDef.equations from rfl,
      negativeDef_equations]; exact List.mem_singleton_self _)
    (fun i => [q, p].getD i.val p)
    (fun j => match j with
      | ⟨0, _⟩ => hq
      | ⟨1, _⟩ => hp)
    (tNegative adm member (tEvidence adm memberEv hp hq)) hq

/-- The statement that a packet is the packet of its counts is a type. -/
theorem tEtaAt (memberEv : Declaration.datatype evidenceDecl ∈ ds)
    (memberPos : Declaration.definition (.recursive positiveDef) ∈ ds)
    (memberNeg : Declaration.definition (.recursive negativeDef) ∈ ds) {e : CTm Tower.Head n}
    (he : CTyped (withDeclarations objectChurch ds) Γ e cEvidence) :
    CTyped (withDeclarations objectChurch ds) Γ (etaAt e) cU0 :=
  tId (withDeclarations_base _ ds) (tEvidenceType adm memberEv)
    (tEvidence adm memberEv (tPositive adm memberPos he) (tNegative adm memberNeg he)) he

end Declared

/-- Membership of a declaration in a written list. -/
macro "member_tac" : tactic =>
  `(tactic| repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem))

/-! ## The rest of the program is admissible -/

/-- The one constructor of evidence counts. -/
theorem evidenceCtors_entry {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : evidenceCtors[i]? = some (k, fields)) :
    k = evidenceN ∧ fields = [.closed (.const numN), .closed (.const numN)] := by
  match i, entry with
  | 0, entry =>
    obtain ⟨same, sameFields⟩ := Prod.mk.inj (Option.some.inj entry)
    exact ⟨same.symm, sameFields.symm⟩
  | i + 1, entry => exact nomatch entry

/-- The context of a right side at the packet: its two counts. -/
theorem countsCtx_formed {R' : Rules Tower.Head} {B : ChurchRules R'}
    (sub : ChurchRulesSub objectChurch B) :
    CCtxFormed B (CCtx.snoc (.snoc .nil cnum) cnum : CCtx Tower.Head 2) :=
  .snoc (.snoc .nil ⟨_, uSort sub _, tNum sub⟩) ⟨_, uSort sub _, tNum sub⟩

/-- A projection of a packet is admissible over a package with evidence counts. -/
theorem projection_admissible {ds : List (Declaration Tower.Head)}
    (adm : AdmissibleDeclarations objectChurch ds)
    (memberEv : Declaration.datatype evidenceDecl ∈ ds) (name : DeclName) (keep : Fin 2)
    (new : (withDeclarations objectChurch ds).constantType name = none) :
    RecursiveDefinition.Admissible (withDeclarations objectChurch ds)
      { name := name, datatype := evidenceDecl, width := 1, later := .nil, result := cnum,
        body := projectionBody keep } where
  new := new
  typeFormed := ⟨_, uSort (withDeclarations_base _ ds) _,
    tPi (withDeclarations_base _ ds) (tEvidenceType adm memberEv) (tNum (withDeclarations_base _
        ds))⟩
  family := ⟨_, uSort (withDeclarations_base _ ds) _, tNum (withDeclarations_base _ ds)⟩
  formed := fun entry => by
    obtain ⟨rfl, rfl⟩ := evidenceCtors_entry entry
    exact countsCtx_formed (withDeclarations_base _ ds)
  resultType := fun entry => by
    obtain ⟨rfl, rfl⟩ := evidenceCtors_entry entry
    exact (⟨_, uSort (withDeclarations_base _ ds) _, tNum (withDeclarations_base _ ds)⟩ :
      CIsType (withDeclarations objectChurch ds) (CCtx.snoc (.snoc .nil cnum) cnum : CCtx Tower.Head
          2) cnum)
  bodies := fun entry => by
    obtain ⟨rfl, rfl⟩ := evidenceCtors_entry entry
    have typed : ∀ keep : Fin 2, CTyped (withDeclarations objectChurch ds)
        (CCtx.snoc (.snoc .nil cnum) cnum : CCtx Tower.Head 2) (.var keep) cnum := by
      intro keep
      match keep with
      | 0 => exact .var 0
      | 1 => exact .var 1
    exact typed keep

theorem stage5_admissible : AdmissibleDeclarations objectChurch stage5 :=
  ⟨stage4_admissible, List.mem_cons_of_mem _ List.mem_cons_self,
    projection_admissible stage4_admissible (List.mem_cons_of_mem _ List.mem_cons_self)
      positiveN 1 (by decide)⟩

theorem stage6_admissible : AdmissibleDeclarations objectChurch stage6 :=
  ⟨stage5_admissible, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
    projection_admissible stage5_admissible
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) negativeN 0
      (by decide)⟩


/-- The base and the step of the proof that a packet is the packet of its counts: at a
packet, reflexivity, since its two counts compute to its two fields. -/
theorem etaBody_typed :
    CTyped (withDeclarations objectChurch stage6) (CCtx.snoc (.snoc .nil cnum) cnum : CCtx
        Tower.Head 2)
      (.refl (cevidence (.var 1) (.var 0))) (etaAt (cevidence (.var 1) (.var 0))) := by
  have first : CTyped (withDeclarations objectChurch stage6)
      (CCtx.snoc (.snoc .nil cnum) cnum : CCtx Tower.Head 2) (.var 1) cnum := .var 1
  have second : CTyped (withDeclarations objectChurch stage6)
      (CCtx.snoc (.snoc .nil cnum) cnum : CCtx Tower.Head 2) (.var 0) cnum := .var 0
  have packet := tEvidence stage6_admissible (by member_tac) first second
  have computed : CEqual (withDeclarations objectChurch stage6)
      (CCtx.snoc (.snoc .nil cnum) cnum : CCtx Tower.Head 2) (etaAt (cevidence (.var 1) (.var 0)))
      (.id cEvidence (cevidence (.var 1) (.var 0)) (cevidence (.var 1) (.var 0))) cU0 :=
    .idCong (.refl (tEvidenceType stage6_admissible (by member_tac))) (LevelTower.IsUniverse.sort _)
      (eEvidence stage6_admissible (by member_tac)
        (ePositive stage6_admissible (by member_tac) (by member_tac) first second)
        (eNegative stage6_admissible (by member_tac) (by member_tac) first second))
      (.refl packet)
  exact .conv (.reflIntro packet) (.symm computed) (LevelTower.IsUniverse.sort _)

theorem evidenceEtaDef_admissible :
    evidenceEtaDef.Admissible (withDeclarations objectChurch stage6) where
  new := by decide
  typeFormed := ⟨_, LevelTower.IsUniverse.sort _,
    tPi (withDeclarations_base _ stage6) (tEvidenceType stage6_admissible (by member_tac))
      (tEtaAt stage6_admissible (by member_tac) (by member_tac) (by member_tac) (.var 0))⟩
  family := ⟨_, LevelTower.IsUniverse.sort _,
    tEtaAt stage6_admissible (by member_tac) (by member_tac) (by member_tac) (.var 0)⟩
  formed := fun entry => by
    obtain ⟨rfl, rfl⟩ := evidenceCtors_entry entry
    exact countsCtx_formed (withDeclarations_base _ stage6)
  resultType := fun entry => by
    obtain ⟨rfl, rfl⟩ := evidenceCtors_entry entry
    exact (⟨_, LevelTower.IsUniverse.sort _,
      tEtaAt stage6_admissible (by member_tac) (by member_tac) (by member_tac)
        (tEvidence stage6_admissible (by member_tac)
          (.var 1 : CTyped (withDeclarations objectChurch stage6)
            (CCtx.snoc (.snoc .nil cnum) cnum : CCtx Tower.Head 2) (.var 1) cnum) (.var 0))⟩ :
      CIsType (withDeclarations objectChurch stage6) (CCtx.snoc (.snoc .nil cnum) cnum : CCtx
          Tower.Head 2)
        (etaAt (cevidence (.var 1) (.var 0))))
  bodies := fun entry => by
    obtain ⟨rfl, rfl⟩ := evidenceCtors_entry entry
    exact etaBody_typed

theorem stage7_admissible : AdmissibleDeclarations objectChurch stage7 :=
  ⟨stage6_admissible, by member_tac, evidenceEtaDef_admissible⟩

theorem tensorDef_admissible : tensorDef.Admissible (withDeclarations objectChurch stage7) where
  new := by decide
  formed :=
    .snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, tEvidenceType stage7_admissible (by
        member_tac)⟩)
      ⟨_, LevelTower.IsUniverse.sort _, tEvidenceType stage7_admissible (by member_tac)⟩
  resultType :=
    ⟨_, LevelTower.IsUniverse.sort _, tEvidenceType stage7_admissible (by member_tac)⟩
  body := by
    have first : CTyped (withDeclarations objectChurch stage7)
        (CCtx.snoc (.snoc .nil cEvidence) cEvidence : CCtx Tower.Head 2) (.var 1) cEvidence := .var
            1
    have second : CTyped (withDeclarations objectChurch stage7)
        (CCtx.snoc (.snoc .nil cEvidence) cEvidence : CCtx Tower.Head 2) (.var 0) cEvidence := .var
            0
    exact tEvidence stage7_admissible (by member_tac)
      (tMul stage7_admissible (by member_tac) (tPositive stage7_admissible (by member_tac) first)
        (tPositive stage7_admissible (by member_tac) second))
      (tMul stage7_admissible (by member_tac) (tNegative stage7_admissible (by member_tac) first)
        (tNegative stage7_admissible (by member_tac) second))

theorem stage8_admissible : AdmissibleDeclarations objectChurch stage8 :=
  ⟨stage7_admissible, tensorDef_admissible⟩

theorem numberWeightDef_admissible :
    numberWeightDef.Admissible (withDeclarations objectChurch stage8) where
  new := by decide
  formed := .snoc .nil ⟨_, LevelTower.IsUniverse.sort _, tNum (withDeclarations_base _ stage8)⟩
  resultType := ⟨_, LevelTower.IsUniverse.sort _, tNum (withDeclarations_base _ stage8)⟩
  body := (.var 0 : CTyped (withDeclarations objectChurch stage8) (CCtx.snoc .nil cnum) (.var 0)
      cnum)

theorem stage9_admissible : AdmissibleDeclarations objectChurch stage9 :=
  ⟨stage8_admissible, numberWeightDef_admissible⟩

theorem countWeightDef_admissible :
    countWeightDef.Admissible (withDeclarations objectChurch stage9) where
  new := by decide
  formed := .snoc .nil ⟨_, LevelTower.IsUniverse.sort _, tNum (withDeclarations_base _ stage9)⟩
  resultType :=
    ⟨_, LevelTower.IsUniverse.sort _, tEvidenceType stage9_admissible (by member_tac)⟩
  body := by
    have number : CTyped (withDeclarations objectChurch stage9) (CCtx.snoc .nil cnum : CCtx
        Tower.Head 1)
        (.var 0) cnum := .var 0
    exact tEvidence stage9_admissible (by member_tac) number (tOne (withDeclarations_base _ stage9))

/-- **The weight program is an admissible list of declarations** over the object package. -/
theorem weightProgram_admissible : AdmissibleDeclarations objectChurch weightProgram :=
  ⟨stage9_admissible, countWeightDef_admissible⟩


/-! ## Addition is associative, in the object package -/

section AddAssoc

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- The statement for variables `a` and `b`, as a family over the numbers `c`. -/
abbrev assocFamily (i j : Fin n) : CTm Tower.Head n :=
  .lam cnum (.id cnum (cadd (cadd (.var i.succ) (.var j.succ)) (.var 0))
    (cadd (.var i.succ) (cadd (.var j.succ) (.var 0))))

theorem assocBody_typed {i j : Fin n} (ha : CTyped objectChurch Γ (.var i) cnum)
    (hb : CTyped objectChurch Γ (.var j) cnum) :
    CTyped objectChurch (.snoc Γ cnum) (.id cnum (cadd (cadd (.var i.succ) (.var j.succ)) (.var 0))
      (cadd (.var i.succ) (cadd (.var j.succ) (.var 0)))) cU0 :=
  cidT cnum_typed (cadd_typed (cadd_typed (CTyped.weaken ha) (CTyped.weaken hb)) (.var 0))
    (cadd_typed (CTyped.weaken ha) (cadd_typed (CTyped.weaken hb) (.var 0)))

theorem assocFamily_typed {i j : Fin n} (ha : CTyped objectChurch Γ (.var i) cnum)
    (hb : CTyped objectChurch Γ (.var j) cnum) :
    CTyped objectChurch Γ (assocFamily i j) (.pi cnum cU0) :=
  .lamIntro cnum_typed (.sort _) (cpiT (craise cnum_typed) cU0_typed) (.sort _)
    (assocBody_typed ha hb)

theorem assocFamily_at {i j : Fin n} (ha : CTyped objectChurch Γ (.var i) cnum)
    (hb : CTyped objectChurch Γ (.var j) cnum) {t : CTm Tower.Head n}
    (ht : CTyped objectChurch Γ t cnum) :
    CEqual objectChurch Γ (.app (assocFamily i j) t)
      (.id cnum (cadd (cadd (.var i) (.var j)) t) (cadd (.var i) (cadd (.var j) t))) cU0 :=
  .betaPi (A := cnum) (B := cU0)
    (body := .id cnum (cadd (cadd (.var i.succ) (.var j.succ)) (.var 0))
      (cadd (.var i.succ) (cadd (.var j.succ) (.var 0))))
    (a := t) (cpiT (craise cnum_typed) cU0_typed) (.sort _) (assocBody_typed ha hb) ht

/-- The base: both sides compute to `a + b`. -/
theorem assocBase_typed {i j : Fin n} (ha : CTyped objectChurch Γ (.var i) cnum)
    (hb : CTyped objectChurch Γ (.var j) cnum) :
    CTyped objectChurch Γ (.refl (cadd (.var i) (.var j))) (.app (assocFamily i j) czero) := by
  have computed : CEqual objectChurch Γ
      (.id cnum (cadd (cadd (.var i) (.var j)) czero) (cadd (.var i) (cadd (.var j) czero)))
      (.id cnum (cadd (.var i) (.var j)) (cadd (.var i) (.var j))) cU0 :=
    .idCong (.refl cnum_typed) (.sort _) (cadd_zero (cadd_typed ha hb))
      (.appCong (B := cnum) (.refl (.appElim (B := .pi cnum cnum) caddConst_typed ha))
        (cadd_zero hb))
  exact .conv (.reflIntro (cadd_typed ha hb))
    (.symm (.trans (assocFamily_at ha hb czero_typed) computed)) (.sort _)

/-- The step: the congruence of the hypothesis under the successor. -/
abbrev assocStepBody (i j : Fin n) : CTm Tower.Head (n + 2) :=
  congOf cnum cnum (.const sucN) (cadd (cadd (.var i.succ.succ) (.var j.succ.succ)) (.var 1))
    (cadd (.var i.succ.succ) (cadd (.var j.succ.succ) (.var 1))) (.var 0)

theorem assocStepBody_typed {i j : Fin n} (ha : CTyped objectChurch Γ (.var i) cnum)
    (hb : CTyped objectChurch Γ (.var j) cnum) :
    CTyped objectChurch (.snoc (.snoc Γ cnum) (.app (assocFamily i.succ j.succ) (.var 0)))
      (assocStepBody i j) (.app (assocFamily i.succ.succ j.succ.succ) (csuc (.var 1))) := by
  have first : CTyped objectChurch
      (.snoc (.snoc Γ cnum) (.app (assocFamily i.succ j.succ) (.var 0))) (.var i.succ.succ) cnum :=
    CTyped.weaken (CTyped.weaken ha)
  have second : CTyped objectChurch
      (.snoc (.snoc Γ cnum) (.app (assocFamily i.succ j.succ) (.var 0))) (.var j.succ.succ) cnum :=
    CTyped.weaken (CTyped.weaken hb)
  have number : CTyped objectChurch
      (.snoc (.snoc Γ cnum) (.app (assocFamily i.succ j.succ) (.var 0))) (.var 1) cnum := .var 1
  have hypothesis : CTyped objectChurch
      (.snoc (.snoc Γ cnum) (.app (assocFamily i.succ j.succ) (.var 0))) (.var 0)
      (.id cnum (cadd (cadd (.var i.succ.succ) (.var j.succ.succ)) (.var 1))
        (cadd (.var i.succ.succ) (cadd (.var j.succ.succ) (.var 1)))) :=
    .conv (.var 0) (assocFamily_at first second number) (.sort _)
  have congruent := cong_suc (cadd_typed (cadd_typed first second) number)
    (cadd_typed first (cadd_typed second number)) hypothesis
  have computed : CEqual objectChurch
      (.snoc (.snoc Γ cnum) (.app (assocFamily i.succ j.succ) (.var 0)))
      (.id cnum (cadd (cadd (.var i.succ.succ) (.var j.succ.succ)) (csuc (.var 1)))
        (cadd (.var i.succ.succ) (cadd (.var j.succ.succ) (csuc (.var 1)))))
      (.id cnum (csuc (cadd (cadd (.var i.succ.succ) (.var j.succ.succ)) (.var 1)))
        (csuc (cadd (.var i.succ.succ) (cadd (.var j.succ.succ) (.var 1))))) cU0 :=
    .idCong (.refl cnum_typed) (.sort _) (cadd_suc (cadd_typed first second) number)
      (.trans (.appCong (B := cnum) (.refl (.appElim (B := .pi cnum cnum) caddConst_typed first))
        (cadd_suc second number))
        (cadd_suc first (cadd_typed second number)))
  exact .conv congruent
    (.symm (.trans (assocFamily_at first second (csuc_typed number)) computed)) (.sort _)

abbrev assocStep (i j : Fin n) : CTm Tower.Head n :=
  .lam cnum (.lam (.app (assocFamily i.succ j.succ) (.var 0)) (assocStepBody i j))

theorem assocStep_typed {i j : Fin n} (ha : CTyped objectChurch Γ (.var i) cnum)
    (hb : CTyped objectChurch Γ (.var j) cnum) :
    CTyped objectChurch Γ (assocStep i j)
      (.pi cnum (.pi (.app (assocFamily i.succ j.succ) (.var 0))
        (.app (assocFamily i.succ.succ j.succ.succ) (csuc (.var 1))))) := by
  have first : CTyped objectChurch (.snoc Γ cnum) (.var i.succ) cnum := CTyped.weaken ha
  have second : CTyped objectChurch (.snoc Γ cnum) (.var j.succ) cnum := CTyped.weaken hb
  have hypType : CTyped objectChurch (.snoc Γ cnum) (.app (assocFamily i.succ j.succ) (.var 0))
      cU0 :=
    .appElim (B := cU0) (assocFamily_typed first second) (.var 0)
  have goalType : CTyped objectChurch
      (.snoc (.snoc Γ cnum) (.app (assocFamily i.succ j.succ) (.var 0)))
      (.app (assocFamily i.succ.succ j.succ.succ) (csuc (.var 1))) cU0 :=
    .appElim (B := cU0) (assocFamily_typed (CTyped.weaken first) (CTyped.weaken second))
      (csuc_typed (.var 1))
  have inner := cpiT hypType goalType
  exact .lamIntro cnum_typed (.sort _) (cpiT cnum_typed inner) (.sort _)
    (.lamIntro hypType (.sort _) inner (.sort _) (assocStepBody_typed ha hb))

/-- The proof, as a term: for `a`, `b` and `c`, the recursor on `c`. -/
abbrev addAssocProof : CTm Tower.Head n :=
  .lam cnum (.lam cnum (.lam cnum
    (cRecApp (assocFamily 2 1) (.refl (cadd (.var 2) (.var 1))) (assocStep 2 1) (.var 0))))

/-- The statement of associativity of addition. -/
abbrev addAssocStatement : CTm Tower.Head n :=
  .pi cnum (.pi cnum (.pi cnum
    (.id cnum (cadd (cadd (.var 2) (.var 1)) (.var 0)) (cadd (.var 2) (cadd (.var 1) (.var 0))))))

/-- **Addition is associative**, by induction on the third number, in the object package. -/
theorem add_assoc_identity : CTyped objectChurch Γ addAssocProof addAssocStatement := by
  have first : CTyped objectChurch (.snoc (.snoc (.snoc Γ cnum) cnum) cnum) (.var 2) cnum := .var 2
  have second : CTyped objectChurch (.snoc (.snoc (.snoc Γ cnum) cnum) cnum) (.var 1) cnum :=
    .var 1
  have body : CTyped objectChurch (.snoc (.snoc (.snoc Γ cnum) cnum) cnum)
      (cRecApp (assocFamily 2 1) (.refl (cadd (.var 2) (.var 1))) (assocStep 2 1) (.var 0))
      (.id cnum (cadd (cadd (.var 2) (.var 1)) (.var 0)) (cadd (.var 2) (cadd (.var 1)
          (.var 0)))) :=
    .conv (numRec_typed (assocFamily_typed first second) (assocBase_typed first second)
      (assocStep_typed first second) (.var 0)) (assocFamily_at first second (.var 0)) (.sort _)
  have inner3 : CTyped objectChurch (.snoc (.snoc Γ cnum) cnum)
      (.pi cnum (.id cnum (cadd (cadd (.var 2) (.var 1)) (.var 0))
        (cadd (.var 2) (cadd (.var 1) (.var 0))))) cU0 :=
    cpiT cnum_typed (cidT cnum_typed (cadd_typed (cadd_typed first second) (.var 0))
      (cadd_typed first (cadd_typed second (.var 0))))
  have inner2 : CTyped objectChurch (.snoc Γ cnum)
      (.pi cnum (.pi cnum (.id cnum (cadd (cadd (.var 2) (.var 1)) (.var 0))
        (cadd (.var 2) (cadd (.var 1) (.var 0)))))) cU0 :=
    cpiT cnum_typed inner3
  exact .lamIntro cnum_typed (.sort _) (cpiT cnum_typed inner2) (.sort _)
    (.lamIntro cnum_typed (.sort _) inner2 (.sort _)
      (.lamIntro cnum_typed (.sort _) inner3 (.sort _) body))

end AddAssoc


/-! ## The recursion of the product computes, in the object package -/

section MulRec

/-- The parameters of the recursion of the product by `a`. -/
theorem mulRec_mor {n : Nat} {Γ : CCtx Tower.Head n} {a : CTm Tower.Head n}
    (ha : CTyped objectChurch Γ a cnum) :
    CSubstMor objectChurch cRecTele Γ (fun i => [mulStep a, czero, mulMotive].getD i.val
        mulMotive) :=
  fun j => match j with
    | ⟨0, _⟩ => mulStep_typed ha
    | ⟨1, _⟩ => .conv czero_typed (.symm (mulMotive_at czero_typed)) (.sort _)
    | ⟨2, _⟩ => mulMotive_typed

/-- At zero the recursion of the product is zero. -/
theorem mulRec_zero :
    CEqual objectChurch (CCtx.snoc .nil cnum : CCtx Tower.Head 1)
      (cRecApp mulMotive czero (mulStep (.var 0)) czero) czero cnum := by
  have zeroCase : CTyped objectChurch (CCtx.snoc .nil cnum : CCtx Tower.Head 1) czero
      (.app mulMotive czero) := .conv czero_typed (.symm (mulMotive_at czero_typed)) (.sort _)
  have iota : CEqual objectChurch (CCtx.snoc .nil cnum : CCtx Tower.Head 1)
      (cRecApp mulMotive czero (mulStep (.var 0)) czero) czero (.app mulMotive czero) :=
    .rootAdmitted (cnumRecZero_step mulMotive czero (mulStep (.var 0)))
      (cnumRecZero_admits (mulRec_mor (.var 0)))
      (numRec_typed mulMotive_typed zeroCase (mulStep_typed (.var 0)) czero_typed) zeroCase
  exact .convEq iota (mulMotive_at czero_typed) (.sort _)

/-- At a successor the recursion of the product is the recursion at the predecessor plus
`a`. -/
theorem mulRec_suc :
    CEqual objectChurch (CCtx.snoc (.snoc .nil cnum) cnum : CCtx Tower.Head 2)
      (cRecApp mulMotive czero (mulStep (.var 1)) (csuc (.var 0)))
      (cadd (cRecApp mulMotive czero (mulStep (.var 1)) (.var 0)) (.var 1)) cnum := by
  have zeroCase : CTyped objectChurch (CCtx.snoc (.snoc .nil cnum) cnum : CCtx Tower.Head 2) czero
      (.app mulMotive czero) := .conv czero_typed (.symm (mulMotive_at czero_typed)) (.sort _)
  have recAt : CTyped objectChurch (CCtx.snoc (.snoc .nil cnum) cnum : CCtx Tower.Head 2)
      (cRecApp mulMotive czero (mulStep (.var 1)) (.var 0)) (.app mulMotive (.var 0)) :=
    numRec_typed mulMotive_typed zeroCase (mulStep_typed (.var 1)) (.var 0)
  have stepAt : CTyped objectChurch (CCtx.snoc (.snoc .nil cnum) cnum : CCtx Tower.Head 2)
      (.app (.app (mulStep (.var 1)) (.var 0)) (cRecApp mulMotive czero (mulStep (.var 1))
          (.var 0)))
      (.app mulMotive (csuc (.var 0))) :=
    .appElim (B := .app mulMotive (csuc (.var 1)))
      (.appElim (B := .pi (.app mulMotive (.var 0)) (.app mulMotive (csuc (.var 1))))
        (mulStep_typed (.var 1)) (.var 0)) recAt
  have iota : CEqual objectChurch (CCtx.snoc (.snoc .nil cnum) cnum : CCtx Tower.Head 2)
      (cRecApp mulMotive czero (mulStep (.var 1)) (csuc (.var 0)))
      (.app (.app (mulStep (.var 1)) (.var 0)) (cRecApp mulMotive czero (mulStep (.var 1))
          (.var 0)))
      (.app mulMotive (csuc (.var 0))) :=
    .rootAdmitted (cnumRecSuc_step mulMotive czero (mulStep (.var 1)) (.var 0))
      (cnumRecSuc_admits
        (CSubstEq.cons ⟨mulRec_mor (.var 1), fun i => .refl (mulRec_mor (.var 1) i)⟩
          (.var 0) (.refl (.var 0))).1)
      (numRec_typed mulMotive_typed zeroCase (mulStep_typed (.var 1)) (csuc_typed (.var 0))) stepAt
  have first : CEqual objectChurch (CCtx.snoc (.snoc .nil cnum) cnum : CCtx Tower.Head 2)
      (.app (mulStep (.var 1)) (.var 0)) (mulInner (.var 1))
      (.pi (.app mulMotive (.var 0)) (.app mulMotive (csuc (.var 1)))) :=
    .betaPi (A := cnum) (B := .pi (.app mulMotive (.var 0)) (.app mulMotive (csuc (.var 1))))
      (body := mulInner (.var 2)) (a := .var 0)
      (cpiT cnum_typed mulInnerPi_typed) (.sort _) (mulInner_typed (.var 2)) (.var 0)
  have second : CEqual objectChurch (CCtx.snoc (.snoc .nil cnum) cnum : CCtx Tower.Head 2)
      (.app (mulInner (.var 1)) (cRecApp mulMotive czero (mulStep (.var 1)) (.var 0)))
      (cadd (cRecApp mulMotive czero (mulStep (.var 1)) (.var 0)) (.var 1))
      (.app mulMotive (csuc (.var 0))) :=
    .betaPi (A := .app mulMotive (.var 0)) (B := .app mulMotive (csuc (.var 1)))
      (body := cadd (.var 0) (.var 2)) (a := cRecApp mulMotive czero (mulStep (.var 1)) (.var 0))
      mulInnerPi_typed (.sort _) (mulInnerBody_typed (a := .var 1) (.var 1)) recAt
  exact .convEq (.trans iota (.trans (.appCong first (.refl recAt)) second))
    (mulMotive_at (csuc_typed (.var 0))) (.sort _)

end MulRec

/-! ## The toolkit of the weight package -/

section Weights

variable {n : Nat} {Γ : CCtx Tower.Head n}

theorem subW : ChurchRulesSub objectChurch weights := withDeclarations_base objectChurch
    weightProgram

theorem wMul {a b : CTm Tower.Head n} (ha : CTyped weights Γ a cnum) (hb : CTyped weights Γ b
    cnum) :
    CTyped weights Γ (cmul a b) cnum :=
  tMul weightProgram_admissible (by member_tac) ha hb

theorem wMulStep {a : CTm Tower.Head n} (ha : CTyped weights Γ a cnum) :
    CTyped weights Γ (mulStep a)
      (.pi cnum (.pi (.app mulMotive (.var 0)) (.app mulMotive (csuc (.var 1))))) :=
  CTyped.substitute ((mulStep_typed (Γ := CCtx.snoc .nil cnum) (.var 0)).mono subW)
    (σ := fun _ => a) (fun j => match j with | ⟨0, _⟩ => ha)

theorem wMotiveAt {t : CTm Tower.Head n} (ht : CTyped weights Γ t cnum) :
    CEqual weights Γ (.app mulMotive t) cnum cU0 :=
  .betaPi (A := cnum) (B := cU0) (body := cnum) (a := t)
    (tPi subW (tRaise subW (tNum subW)) (tU0 subW)) (uSort subW _) (tNum subW) ht

/-- **The product unfolds** to the recursion of its definition. -/
theorem wMulUnfold {a b : CTm Tower.Head n} (ha : CTyped weights Γ a cnum)
    (hb : CTyped weights Γ b cnum) :
    CEqual weights Γ (cmul a b) (cRecApp mulMotive czero (mulStep a) b) cnum := by
  have zeroCase : CTyped weights Γ czero (.app mulMotive czero) :=
    .conv (tZero subW) (.symm (wMotiveAt (tZero subW))) (uSort subW _)
  have right : CTyped weights Γ (cRecApp mulMotive czero (mulStep a) b) cnum :=
    .conv (tRec subW (mulMotive_typed.mono subW) zeroCase (wMulStep ha) hb) (wMotiveAt hb)
      (uSort subW _)
  exact definition_equation_holds (D := .explicit mulDef) (by member_tac) (e := mulEquation)
    (by rw [show Definition.equations (.explicit mulDef) = mulDef.equations from rfl,
      mulDef_equations]; exact List.mem_singleton_self _)
    (fun i => [b, a].getD i.val a)
    (fun j => match j with
      | ⟨0, _⟩ => hb
      | ⟨1, _⟩ => ha)
    (wMul ha hb) right

/-- **A number times zero is zero**, in the judgment. -/
theorem wMulZero {a : CTm Tower.Head n} (ha : CTyped weights Γ a cnum) :
    CEqual weights Γ (cmul a czero) czero cnum :=
  .trans (wMulUnfold ha (tZero subW))
    (CEqual.substitute (mulRec_zero.mono subW) (σ := fun _ => a)
      (fun j => match j with | ⟨0, _⟩ => ha))

/-- **A number times a successor is the number times the predecessor, plus the number.** -/
theorem wMulSuc {a b : CTm Tower.Head n} (ha : CTyped weights Γ a cnum)
    (hb : CTyped weights Γ b cnum) :
    CEqual weights Γ (cmul a (csuc b)) (cadd (cmul a b) a) cnum :=
  .trans (wMulUnfold ha (tSuc subW hb))
    (.trans (CEqual.substitute (mulRec_suc.mono subW) (σ := fun i => [b, a].getD i.val a)
      (fun j => match j with
        | ⟨0, _⟩ => hb
        | ⟨1, _⟩ => ha))
      (eAdd subW (.symm (wMulUnfold ha hb)) (.refl ha)))

/-- The product is a congruence of the judgment's equality. -/
theorem eMul {a a' b b' : CTm Tower.Head n} (ea : CEqual weights Γ a a' cnum)
    (eb : CEqual weights Γ b b' cnum) : CEqual weights Γ (cmul a b) (cmul a' b') cnum :=
  .appCong (B := cnum) (.appCong (B := .pi cnum cnum)
    (.refl (weightProgram_admissible.definition_typed ConvRules.objectLevels
      (D := .explicit mulDef) (by member_tac))) ea) eb

end Weights


/-! ## The laws of the product of numbers -/

section NumberLaws

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- The congruence of identity proofs under the successor, in the weight package. -/
theorem wCongSuc {x y p : CTm Tower.Head n} (hx : CTyped weights Γ x cnum)
    (hy : CTyped weights Γ y cnum) (hp : CTyped weights Γ p (.id cnum x y)) :
    CTyped weights Γ (congOf cnum cnum (.const sucN) x y p) (.id cnum (csuc x) (csuc y)) :=
  tCong subW (tNum subW) (tNum subW) (csucConst_typed.mono subW) hx hy hp

/-- Adding a fixed number on the right. -/
abbrev addRight (A : CTm Tower.Head n) : CTm Tower.Head n := .lam cnum (cadd (.var 0) (A.rename wk))

/-- The congruence of identity proofs under adding a fixed number on the right. -/
theorem wCongAddRight {A x y p : CTm Tower.Head n} (hA : CTyped weights Γ A cnum)
    (hx : CTyped weights Γ x cnum) (hy : CTyped weights Γ y cnum)
    (hp : CTyped weights Γ p (.id cnum x y)) :
    CTyped weights Γ (congOf cnum cnum (addRight A) x y p) (.id cnum (cadd x A) (cadd y A)) := by
  have body : CTyped weights (.snoc Γ cnum) (cadd (.var 0) (A.rename wk)) cnum :=
    tAdd subW (.var 0) (CTyped.weaken hA)
  have fnType : CTyped weights Γ (.pi cnum cnum) cU0 := tPi subW (tNum subW) (tNum subW)
  have fn : CTyped weights Γ (addRight A) (.pi cnum (cnum.rename wk)) :=
    .lamIntro (tNum subW) (uSort subW _) fnType (uSort subW _) body
  have congruent := tCong subW (tNum subW) (tNum subW) fn hx hy hp
  have atX : CEqual weights Γ (.app (addRight A) x) (cadd x A) cnum := by
    have beta := CDerivable.betaPi (A := cnum) (B := cnum) (body := cadd (.var 0) (A.rename wk))
      (a := x) fnType (uSort subW _) body hx
    have same : CTm.inst0 x (cadd (.var 0) (A.rename wk) : CTm Tower.Head (n + 1)) = cadd x A := by
      show cadd x (CTm.inst0 x (A.rename wk)) = cadd x A
      rw [CTm.inst0_rename_wk]
    rw [same] at beta
    exact beta
  have atY : CEqual weights Γ (.app (addRight A) y) (cadd y A) cnum := by
    have beta := CDerivable.betaPi (A := cnum) (B := cnum) (body := cadd (.var 0) (A.rename wk))
      (a := y) fnType (uSort subW _) body hy
    have same : CTm.inst0 y (cadd (.var 0) (A.rename wk) : CTm Tower.Head (n + 1)) = cadd y A := by
      show cadd y (CTm.inst0 y (A.rename wk)) = cadd y A
      rw [CTm.inst0_rename_wk]
    rw [same] at beta
    exact beta
  exact .conv congruent (.idCong (.refl (tNum subW)) (uSort subW _) atX atY) (uSort subW _)

/-- **A number times one is the number**: `a * 1` computes to `0 + a`, and the first
induction of the object package proves `0 + a = a`. -/
abbrev mulOneRightProof : CTm Tower.Head n := .lam cnum (.app zeroAddProof (.var 0))

/-- The statement of the right unit law. -/
abbrev mulOneRightStatement : CTm Tower.Head n := .pi cnum (.id cnum (cmul (.var 0) cone) (.var 0))

theorem mul_one_right_identity : CTyped weights Γ mulOneRightProof mulOneRightStatement := by
  have a : CTyped weights (.snoc Γ cnum) (.var 0) cnum := .var 0
  have zeroAdd : CTyped weights (.snoc Γ cnum) (.app zeroAddProof (.var 0))
      (.id cnum (cadd czero (.var 0)) (.var 0)) :=
    .appElim (B := .id cnum (cadd czero (.var 0)) (.var 0)) (zero_add_identity.mono subW) a
  have computed : CEqual weights (.snoc Γ cnum) (.id cnum (cmul (.var 0) cone) (.var 0))
      (.id cnum (cadd czero (.var 0)) (.var 0)) cU0 :=
    .idCong (.refl (tNum subW)) (uSort subW _)
      (.trans (wMulSuc a (tZero subW)) (eAdd subW (wMulZero a) (.refl a))) (.refl a)
  exact .lamIntro (tNum subW) (uSort subW _)
    (tPi subW (tNum subW) (tId subW (tNum subW) (wMul a (tOne subW)) a)) (uSort subW _)
    (.conv zeroAdd (.symm computed) (uSort subW _))

/-! ### One times a number is the number, by induction -/

/-- The statement as a family over the numbers. -/
abbrev oneMulFamily : CTm Tower.Head n := .lam cnum (.id cnum (cmul cone (.var 0)) (.var 0))

theorem oneMulBody_typed :
    CTyped weights (.snoc Γ cnum) (.id cnum (cmul cone (.var 0)) (.var 0)) cU0 :=
  tId subW (tNum subW) (wMul (tOne subW) (.var 0)) (.var 0)

theorem oneMulFamily_typed : CTyped weights Γ oneMulFamily (.pi cnum cU0) :=
  .lamIntro (tNum subW) (uSort subW _) (tPi subW (tRaise subW (tNum subW)) (tU0 subW))
    (uSort subW _) oneMulBody_typed

theorem oneMulFamily_at {t : CTm Tower.Head n} (ht : CTyped weights Γ t cnum) :
    CEqual weights Γ (.app oneMulFamily t) (.id cnum (cmul cone t) t) cU0 :=
  .betaPi (A := cnum) (B := cU0) (body := .id cnum (cmul cone (.var 0)) (.var 0)) (a := t)
    (tPi subW (tRaise subW (tNum subW)) (tU0 subW)) (uSort subW _) oneMulBody_typed ht

theorem oneMulBase_typed : CTyped weights Γ (.refl czero) (.app oneMulFamily czero) := by
  have computed : CEqual weights Γ (.id cnum (cmul cone czero) czero) (.id cnum czero czero) cU0 :=
    .idCong (.refl (tNum subW)) (uSort subW _) (wMulZero (tOne subW)) (.refl (tZero subW))
  exact .conv (.reflIntro (tZero subW))
    (.symm (.trans (oneMulFamily_at (tZero subW)) computed)) (uSort subW _)

abbrev oneMulStepBody : CTm Tower.Head (n + 2) :=
  congOf cnum cnum (.const sucN) (cmul cone (.var 1)) (.var 1) (.var 0)

theorem oneMulStepBody_typed :
    CTyped weights (.snoc (.snoc Γ cnum) (.app oneMulFamily (.var 0))) oneMulStepBody
      (.app oneMulFamily (csuc (.var 1))) := by
  have number : CTyped weights (.snoc (.snoc Γ cnum) (.app oneMulFamily (.var 0))) (.var 1) cnum :=
    .var 1
  have hypothesis : CTyped weights (.snoc (.snoc Γ cnum) (.app oneMulFamily (.var 0))) (.var 0)
      (.id cnum (cmul cone (.var 1)) (.var 1)) :=
    .conv (.var 0) (oneMulFamily_at number) (uSort subW _)
  have congruent := wCongSuc (wMul (tOne subW) number) number hypothesis
  have computed : CEqual weights (.snoc (.snoc Γ cnum) (.app oneMulFamily (.var 0)))
      (.id cnum (cmul cone (csuc (.var 1))) (csuc (.var 1)))
      (.id cnum (csuc (cmul cone (.var 1))) (csuc (.var 1))) cU0 :=
    .idCong (.refl (tNum subW)) (uSort subW _)
      (.trans (wMulSuc (tOne subW) number)
        (.trans (eAddSuc subW (wMul (tOne subW) number) (tZero subW))
          (eSuc subW (eAddZero subW (wMul (tOne subW) number)))))
      (.refl (tSuc subW number))
  exact .conv congruent
    (.symm (.trans (oneMulFamily_at (tSuc subW number)) computed)) (uSort subW _)

abbrev oneMulStep : CTm Tower.Head n :=
  .lam cnum (.lam (.app oneMulFamily (.var 0)) oneMulStepBody)

theorem oneMulStep_typed :
    CTyped weights Γ oneMulStep
      (.pi cnum (.pi (.app oneMulFamily (.var 0)) (.app oneMulFamily (csuc (.var 1))))) := by
  have hypType : CTyped weights (.snoc Γ cnum) (.app oneMulFamily (.var 0)) cU0 :=
    .appElim (B := cU0) oneMulFamily_typed (.var 0)
  have goalType : CTyped weights (.snoc (.snoc Γ cnum) (.app oneMulFamily (.var 0)))
      (.app oneMulFamily (csuc (.var 1))) cU0 :=
    .appElim (B := cU0) oneMulFamily_typed (tSuc subW (.var 1))
  have inner := tPi subW hypType goalType
  exact .lamIntro (tNum subW) (uSort subW _) (tPi subW (tNum subW) inner) (uSort subW _)
    (.lamIntro hypType (uSort subW _) inner (uSort subW _) oneMulStepBody_typed)

abbrev mulOneLeftProof : CTm Tower.Head n :=
  .lam cnum (cRecApp oneMulFamily (.refl czero) oneMulStep (.var 0))

/-- The statement of the left unit law. -/
abbrev mulOneLeftStatement : CTm Tower.Head n := .pi cnum (.id cnum (cmul cone (.var 0)) (.var 0))

/-- **One times a number is the number**, by induction on the number. -/
theorem mul_one_left_identity : CTyped weights Γ mulOneLeftProof mulOneLeftStatement :=
  .lamIntro (tNum subW) (uSort subW _) (tPi subW (tNum subW) oneMulBody_typed) (uSort subW _)
    (.conv (tRec subW oneMulFamily_typed oneMulBase_typed oneMulStep_typed (.var 0))
      (oneMulFamily_at (.var 0)) (uSort subW _))

/-- Associativity of addition at three variables. -/
theorem addAssoc_atVars :
    CTyped objectChurch (CCtx.snoc (.snoc (.snoc .nil cnum) cnum) cnum : CCtx Tower.Head 3)
      (.app (.app (.app addAssocProof (.var 2)) (.var 1)) (.var 0))
      (.id cnum (cadd (cadd (.var 2) (.var 1)) (.var 0)) (cadd (.var 2) (cadd (.var 1)
          (.var 0)))) :=
  have first : CTyped objectChurch (CCtx.snoc (.snoc (.snoc .nil cnum) cnum) cnum : CCtx Tower.Head
      3)
      (.app addAssocProof (.var 2))
      (.pi cnum (.pi cnum (.id cnum (cadd (cadd (.var 4) (.var 1)) (.var 0))
        (cadd (.var 4) (cadd (.var 1) (.var 0)))))) :=
    .appElim (B := .pi cnum (.pi cnum (.id cnum (cadd (cadd (.var 2) (.var 1)) (.var 0))
      (cadd (.var 2) (cadd (.var 1) (.var 0)))))) add_assoc_identity (.var 2)
  have second : CTyped objectChurch (CCtx.snoc (.snoc (.snoc .nil cnum) cnum) cnum : CCtx Tower.Head
      3)
      (.app (.app addAssocProof (.var 2)) (.var 1))
      (.pi cnum (.id cnum (cadd (cadd (.var 3) (.var 2)) (.var 0))
        (cadd (.var 3) (cadd (.var 2) (.var 0))))) :=
    .appElim (B := .pi cnum (.id cnum (cadd (cadd (.var 4) (.var 1)) (.var 0))
      (cadd (.var 4) (cadd (.var 1) (.var 0))))) first (.var 1)
  .appElim (B := .id cnum (cadd (cadd (.var 3) (.var 2)) (.var 0))
    (cadd (.var 3) (cadd (.var 2) (.var 0)))) second (.var 0)

/-- An instance of the associativity of addition, in the weight package. -/
theorem wAddAssoc {x y z : CTm Tower.Head n} (hx : CTyped weights Γ x cnum)
    (hy : CTyped weights Γ y cnum) (hz : CTyped weights Γ z cnum) :
    CTyped weights Γ (.app (.app (.app addAssocProof x) y) z)
      (.id cnum (cadd (cadd x y) z) (cadd x (cadd y z))) :=
  CTyped.substitute (addAssoc_atVars.mono subW) (σ := fun i => [z, y, x].getD i.val x)
    (fun j => match j with
      | ⟨0, _⟩ => hz
      | ⟨1, _⟩ => hy
      | ⟨2, _⟩ => hx)

/-! ### The product distributes over a sum on its right, by induction -/

/-- The statement for variables `a` and `b`, as a family over the numbers `c`:
`a * (b + c) = a * b + a * c`. -/
abbrev distFamily (i j : Fin n) : CTm Tower.Head n :=
  .lam cnum (.id cnum (cmul (.var i.succ) (cadd (.var j.succ) (.var 0)))
    (cadd (cmul (.var i.succ) (.var j.succ)) (cmul (.var i.succ) (.var 0))))

theorem distBody_typed {i j : Fin n} (ha : CTyped weights Γ (.var i) cnum)
    (hb : CTyped weights Γ (.var j) cnum) :
    CTyped weights (.snoc Γ cnum) (.id cnum (cmul (.var i.succ) (cadd (.var j.succ) (.var 0)))
      (cadd (cmul (.var i.succ) (.var j.succ)) (cmul (.var i.succ) (.var 0)))) cU0 :=
  tId subW (tNum subW) (wMul (CTyped.weaken ha) (tAdd subW (CTyped.weaken hb) (.var 0)))
    (tAdd subW (wMul (CTyped.weaken ha) (CTyped.weaken hb)) (wMul (CTyped.weaken ha) (.var 0)))

theorem distFamily_typed {i j : Fin n} (ha : CTyped weights Γ (.var i) cnum)
    (hb : CTyped weights Γ (.var j) cnum) : CTyped weights Γ (distFamily i j) (.pi cnum cU0) :=
  .lamIntro (tNum subW) (uSort subW _) (tPi subW (tRaise subW (tNum subW)) (tU0 subW))
    (uSort subW _) (distBody_typed ha hb)

theorem distFamily_at {i j : Fin n} (ha : CTyped weights Γ (.var i) cnum)
    (hb : CTyped weights Γ (.var j) cnum) {t : CTm Tower.Head n} (ht : CTyped weights Γ t cnum) :
    CEqual weights Γ (.app (distFamily i j) t)
      (.id cnum (cmul (.var i) (cadd (.var j) t)) (cadd (cmul (.var i) (.var j)) (cmul (.var i) t)))
      cU0 :=
  .betaPi (A := cnum) (B := cU0)
    (body := .id cnum (cmul (.var i.succ) (cadd (.var j.succ) (.var 0)))
      (cadd (cmul (.var i.succ) (.var j.succ)) (cmul (.var i.succ) (.var 0))))
    (a := t) (tPi subW (tRaise subW (tNum subW)) (tU0 subW)) (uSort subW _) (distBody_typed ha hb)
        ht

/-- The base: both sides compute to `a * b`. -/
theorem distBase_typed {i j : Fin n} (ha : CTyped weights Γ (.var i) cnum)
    (hb : CTyped weights Γ (.var j) cnum) :
    CTyped weights Γ (.refl (cmul (.var i) (.var j))) (.app (distFamily i j) czero) := by
  have computed : CEqual weights Γ
      (.id cnum (cmul (.var i) (cadd (.var j) czero)) (cadd (cmul (.var i) (.var j)) (cmul (.var i)
          czero)))
      (.id cnum (cmul (.var i) (.var j)) (cmul (.var i) (.var j))) cU0 :=
    .idCong (.refl (tNum subW)) (uSort subW _) (eMul (.refl ha) (eAddZero subW hb))
      (.trans (eAdd subW (.refl (wMul ha hb)) (wMulZero ha)) (eAddZero subW (wMul ha hb)))
  exact .conv (.reflIntro (wMul ha hb))
    (.symm (.trans (distFamily_at ha hb (tZero subW)) computed)) (uSort subW _)

/-- The step: the hypothesis carried under adding `a`, then associativity of addition. -/
abbrev distStepBody (i j : Fin n) : CTm Tower.Head (n + 2) :=
  transOf cnum (cadd (cmul (.var i.succ.succ) (cadd (.var j.succ.succ) (.var 1)))
      (.var i.succ.succ))
    (cadd (cadd (cmul (.var i.succ.succ) (.var j.succ.succ)) (cmul (.var i.succ.succ) (.var 1)))
      (.var i.succ.succ))
    (cadd (cmul (.var i.succ.succ) (.var j.succ.succ))
      (cadd (cmul (.var i.succ.succ) (.var 1)) (.var i.succ.succ)))
    (congOf cnum cnum (addRight (.var i.succ.succ))
      (cmul (.var i.succ.succ) (cadd (.var j.succ.succ) (.var 1)))
      (cadd (cmul (.var i.succ.succ) (.var j.succ.succ)) (cmul (.var i.succ.succ) (.var 1)))
          (.var 0))
    (.app (.app (.app addAssocProof (cmul (.var i.succ.succ) (.var j.succ.succ)))
      (cmul (.var i.succ.succ) (.var 1))) (.var i.succ.succ))

theorem distStepBody_typed {i j : Fin n} (ha : CTyped weights Γ (.var i) cnum)
    (hb : CTyped weights Γ (.var j) cnum) :
    CTyped weights (.snoc (.snoc Γ cnum) (.app (distFamily i.succ j.succ) (.var 0)))
      (distStepBody i j) (.app (distFamily i.succ.succ j.succ.succ) (csuc (.var 1))) := by
  have a : CTyped weights (.snoc (.snoc Γ cnum) (.app (distFamily i.succ j.succ) (.var 0)))
      (.var i.succ.succ) cnum := CTyped.weaken (CTyped.weaken ha)
  have b : CTyped weights (.snoc (.snoc Γ cnum) (.app (distFamily i.succ j.succ) (.var 0)))
      (.var j.succ.succ) cnum := CTyped.weaken (CTyped.weaken hb)
  have k : CTyped weights (.snoc (.snoc Γ cnum) (.app (distFamily i.succ j.succ) (.var 0)))
      (.var 1) cnum := .var 1
  have hypothesis : CTyped weights
      (.snoc (.snoc Γ cnum) (.app (distFamily i.succ j.succ) (.var 0)))
      (.var 0) (.id cnum (cmul (.var i.succ.succ) (cadd (.var j.succ.succ) (.var 1)))
        (cadd (cmul (.var i.succ.succ) (.var j.succ.succ)) (cmul (.var i.succ.succ) (.var 1)))) :=
    .conv (.var 0) (distFamily_at a b k) (uSort subW _)
  have carried := wCongAddRight a (wMul a (tAdd subW b k))
    (tAdd subW (wMul a b) (wMul a k)) hypothesis
  have regrouped := wAddAssoc (wMul a b) (wMul a k) a
  have joined := tTrans subW (tNum subW) (tAdd subW (wMul a (tAdd subW b k)) a)
    (tAdd subW (tAdd subW (wMul a b) (wMul a k)) a)
    (tAdd subW (wMul a b) (tAdd subW (wMul a k) a)) carried regrouped
  have computed : CEqual weights (.snoc (.snoc Γ cnum) (.app (distFamily i.succ j.succ) (.var 0)))
      (.id cnum (cmul (.var i.succ.succ) (cadd (.var j.succ.succ) (csuc (.var 1))))
        (cadd (cmul (.var i.succ.succ) (.var j.succ.succ)) (cmul (.var i.succ.succ) (csuc
            (.var 1)))))
      (.id cnum (cadd (cmul (.var i.succ.succ) (cadd (.var j.succ.succ) (.var 1)))
          (.var i.succ.succ))
        (cadd (cmul (.var i.succ.succ) (.var j.succ.succ))
          (cadd (cmul (.var i.succ.succ) (.var 1)) (.var i.succ.succ)))) cU0 :=
    .idCong (.refl (tNum subW)) (uSort subW _)
      (.trans (eMul (.refl a) (eAddSuc subW b k)) (wMulSuc a (tAdd subW b k)))
      (eAdd subW (.refl (wMul a b)) (wMulSuc a k))
  exact .conv joined
    (.symm (.trans (distFamily_at a b (tSuc subW k)) computed)) (uSort subW _)

abbrev distStep (i j : Fin n) : CTm Tower.Head n :=
  .lam cnum (.lam (.app (distFamily i.succ j.succ) (.var 0)) (distStepBody i j))

theorem distStep_typed {i j : Fin n} (ha : CTyped weights Γ (.var i) cnum)
    (hb : CTyped weights Γ (.var j) cnum) :
    CTyped weights Γ (distStep i j)
      (.pi cnum (.pi (.app (distFamily i.succ j.succ) (.var 0))
        (.app (distFamily i.succ.succ j.succ.succ) (csuc (.var 1))))) := by
  have first : CTyped weights (.snoc Γ cnum) (.var i.succ) cnum := CTyped.weaken ha
  have second : CTyped weights (.snoc Γ cnum) (.var j.succ) cnum := CTyped.weaken hb
  have hypType : CTyped weights (.snoc Γ cnum) (.app (distFamily i.succ j.succ) (.var 0)) cU0 :=
    .appElim (B := cU0) (distFamily_typed first second) (.var 0)
  have goalType : CTyped weights (.snoc (.snoc Γ cnum) (.app (distFamily i.succ j.succ) (.var 0)))
      (.app (distFamily i.succ.succ j.succ.succ) (csuc (.var 1))) cU0 :=
    .appElim (B := cU0) (distFamily_typed (CTyped.weaken first) (CTyped.weaken second))
      (tSuc subW (.var 1))
  have inner := tPi subW hypType goalType
  exact .lamIntro (tNum subW) (uSort subW _) (tPi subW (tNum subW) inner) (uSort subW _)
    (.lamIntro hypType (uSort subW _) inner (uSort subW _) (distStepBody_typed ha hb))

abbrev distProof : CTm Tower.Head n :=
  .lam cnum (.lam cnum (.lam cnum
    (cRecApp (distFamily 2 1) (.refl (cmul (.var 2) (.var 1))) (distStep 2 1) (.var 0))))

/-- The statement of distributivity. -/
abbrev distStatement : CTm Tower.Head n :=
  .pi cnum (.pi cnum (.pi cnum (.id cnum (cmul (.var 2) (cadd (.var 1) (.var 0)))
    (cadd (cmul (.var 2) (.var 1)) (cmul (.var 2) (.var 0))))))

/-- **The product distributes over a sum on its right**, by induction on the last summand. -/
theorem mul_add_identity : CTyped weights Γ distProof distStatement := by
  have first : CTyped weights (.snoc (.snoc (.snoc Γ cnum) cnum) cnum) (.var 2) cnum := .var 2
  have second : CTyped weights (.snoc (.snoc (.snoc Γ cnum) cnum) cnum) (.var 1) cnum := .var 1
  have body : CTyped weights (.snoc (.snoc (.snoc Γ cnum) cnum) cnum)
      (cRecApp (distFamily 2 1) (.refl (cmul (.var 2) (.var 1))) (distStep 2 1) (.var 0))
      (.id cnum (cmul (.var 2) (cadd (.var 1) (.var 0)))
        (cadd (cmul (.var 2) (.var 1)) (cmul (.var 2) (.var 0)))) :=
    .conv (tRec subW (distFamily_typed first second) (distBase_typed first second)
      (distStep_typed first second) (.var 0)) (distFamily_at first second (.var 0)) (uSort subW _)
  have inner3 : CTyped weights (.snoc (.snoc Γ cnum) cnum)
      (.pi cnum (.id cnum (cmul (.var 2) (cadd (.var 1) (.var 0)))
        (cadd (cmul (.var 2) (.var 1)) (cmul (.var 2) (.var 0))))) cU0 :=
    tPi subW (tNum subW) (tId subW (tNum subW) (wMul (.var 2) (tAdd subW (.var 1) (.var 0)))
      (tAdd subW (wMul (.var 2) (.var 1)) (wMul (.var 2) (.var 0))))
  have inner2 : CTyped weights (.snoc Γ cnum)
      (.pi cnum (.pi cnum (.id cnum (cmul (.var 2) (cadd (.var 1) (.var 0)))
        (cadd (cmul (.var 2) (.var 1)) (cmul (.var 2) (.var 0)))))) cU0 :=
    tPi subW (tNum subW) inner3
  exact .lamIntro (tNum subW) (uSort subW _) (tPi subW (tNum subW) inner2) (uSort subW _)
    (.lamIntro (tNum subW) (uSort subW _) inner2 (uSort subW _)
      (.lamIntro (tNum subW) (uSort subW _) inner3 (uSort subW _) body))

/-- Distributivity at three variables. -/
theorem mulAdd_atVars :
    CTyped weights (CCtx.snoc (.snoc (.snoc .nil cnum) cnum) cnum : CCtx Tower.Head 3)
      (.app (.app (.app distProof (.var 2)) (.var 1)) (.var 0))
      (.id cnum (cmul (.var 2) (cadd (.var 1) (.var 0))) (cadd (cmul (.var 2) (.var 1)) (cmul
          (.var 2) (.var 0)))) :=
  have first : CTyped weights (CCtx.snoc (.snoc (.snoc .nil cnum) cnum) cnum : CCtx Tower.Head 3)
      (.app distProof (.var 2))
      (.pi cnum (.pi cnum (.id cnum (cmul (.var 4) (cadd (.var 1) (.var 0)))
        (cadd (cmul (.var 4) (.var 1)) (cmul (.var 4) (.var 0)))))) :=
    .appElim (B := .pi cnum (.pi cnum (.id cnum (cmul (.var 2) (cadd (.var 1) (.var 0)))
      (cadd (cmul (.var 2) (.var 1)) (cmul (.var 2) (.var 0)))))) mul_add_identity (.var 2)
  have second : CTyped weights (CCtx.snoc (.snoc (.snoc .nil cnum) cnum) cnum : CCtx Tower.Head 3)
      (.app (.app distProof (.var 2)) (.var 1))
      (.pi cnum (.id cnum (cmul (.var 3) (cadd (.var 2) (.var 0)))
        (cadd (cmul (.var 3) (.var 2)) (cmul (.var 3) (.var 0))))) :=
    .appElim (B := .pi cnum (.id cnum (cmul (.var 4) (cadd (.var 1) (.var 0)))
      (cadd (cmul (.var 4) (.var 1)) (cmul (.var 4) (.var 0))))) first (.var 1)
  .appElim (B := .id cnum (cmul (.var 3) (cadd (.var 2) (.var 0)))
    (cadd (cmul (.var 3) (.var 2)) (cmul (.var 3) (.var 0)))) second (.var 0)

/-- An instance of distributivity. -/
theorem wMulAdd {x y z : CTm Tower.Head n} (hx : CTyped weights Γ x cnum)
    (hy : CTyped weights Γ y cnum) (hz : CTyped weights Γ z cnum) :
    CTyped weights Γ (.app (.app (.app distProof x) y) z)
      (.id cnum (cmul x (cadd y z)) (cadd (cmul x y) (cmul x z))) :=
  CTyped.substitute mulAdd_atVars (σ := fun i => [z, y, x].getD i.val x)
    (fun j => match j with
      | ⟨0, _⟩ => hz
      | ⟨1, _⟩ => hy
      | ⟨2, _⟩ => hx)

/-! ### The product is associative, by induction -/

/-- The statement for variables `a` and `b`, as a family over the numbers `c`:
`(a * b) * c = a * (b * c)`. -/
abbrev mulAssocFamily (i j : Fin n) : CTm Tower.Head n :=
  .lam cnum (.id cnum (cmul (cmul (.var i.succ) (.var j.succ)) (.var 0))
    (cmul (.var i.succ) (cmul (.var j.succ) (.var 0))))

theorem mulAssocBody_typed {i j : Fin n} (ha : CTyped weights Γ (.var i) cnum)
    (hb : CTyped weights Γ (.var j) cnum) :
    CTyped weights (.snoc Γ cnum) (.id cnum (cmul (cmul (.var i.succ) (.var j.succ)) (.var 0))
      (cmul (.var i.succ) (cmul (.var j.succ) (.var 0)))) cU0 :=
  tId subW (tNum subW) (wMul (wMul (CTyped.weaken ha) (CTyped.weaken hb)) (.var 0))
    (wMul (CTyped.weaken ha) (wMul (CTyped.weaken hb) (.var 0)))

theorem mulAssocFamily_typed {i j : Fin n} (ha : CTyped weights Γ (.var i) cnum)
    (hb : CTyped weights Γ (.var j) cnum) :
    CTyped weights Γ (mulAssocFamily i j) (.pi cnum cU0) :=
  .lamIntro (tNum subW) (uSort subW _) (tPi subW (tRaise subW (tNum subW)) (tU0 subW))
    (uSort subW _) (mulAssocBody_typed ha hb)

theorem mulAssocFamily_at {i j : Fin n} (ha : CTyped weights Γ (.var i) cnum)
    (hb : CTyped weights Γ (.var j) cnum) {t : CTm Tower.Head n} (ht : CTyped weights Γ t cnum) :
    CEqual weights Γ (.app (mulAssocFamily i j) t)
      (.id cnum (cmul (cmul (.var i) (.var j)) t) (cmul (.var i) (cmul (.var j) t))) cU0 :=
  .betaPi (A := cnum) (B := cU0)
    (body := .id cnum (cmul (cmul (.var i.succ) (.var j.succ)) (.var 0))
      (cmul (.var i.succ) (cmul (.var j.succ) (.var 0))))
    (a := t) (tPi subW (tRaise subW (tNum subW)) (tU0 subW)) (uSort subW _)
    (mulAssocBody_typed ha hb) ht

/-- The base: both sides compute to zero. -/
theorem mulAssocBase_typed {i j : Fin n} (ha : CTyped weights Γ (.var i) cnum)
    (hb : CTyped weights Γ (.var j) cnum) :
    CTyped weights Γ (.refl czero) (.app (mulAssocFamily i j) czero) := by
  have computed : CEqual weights Γ
      (.id cnum (cmul (cmul (.var i) (.var j)) czero) (cmul (.var i) (cmul (.var j) czero)))
      (.id cnum czero czero) cU0 :=
    .idCong (.refl (tNum subW)) (uSort subW _) (wMulZero (wMul ha hb))
      (.trans (eMul (.refl ha) (wMulZero hb)) (wMulZero ha))
  exact .conv (.reflIntro (tZero subW))
    (.symm (.trans (mulAssocFamily_at ha hb (tZero subW)) computed)) (uSort subW _)

/-- The step: the hypothesis carried under adding `a * b`, then distributivity turned
round. -/
abbrev mulAssocStepBody (i j : Fin n) : CTm Tower.Head (n + 2) :=
  transOf cnum
    (cadd (cmul (cmul (.var i.succ.succ) (.var j.succ.succ)) (.var 1))
      (cmul (.var i.succ.succ) (.var j.succ.succ)))
    (cadd (cmul (.var i.succ.succ) (cmul (.var j.succ.succ) (.var 1)))
      (cmul (.var i.succ.succ) (.var j.succ.succ)))
    (cmul (.var i.succ.succ) (cadd (cmul (.var j.succ.succ) (.var 1)) (.var j.succ.succ)))
    (congOf cnum cnum (addRight (cmul (.var i.succ.succ) (.var j.succ.succ)))
      (cmul (cmul (.var i.succ.succ) (.var j.succ.succ)) (.var 1))
      (cmul (.var i.succ.succ) (cmul (.var j.succ.succ) (.var 1))) (.var 0))
    (symOf cnum (cmul (.var i.succ.succ) (cadd (cmul (.var j.succ.succ) (.var 1))
        (.var j.succ.succ)))
      (cadd (cmul (.var i.succ.succ) (cmul (.var j.succ.succ) (.var 1)))
        (cmul (.var i.succ.succ) (.var j.succ.succ)))
      (.app (.app (.app distProof (.var i.succ.succ)) (cmul (.var j.succ.succ) (.var 1)))
        (.var j.succ.succ)))

theorem mulAssocStepBody_typed {i j : Fin n} (ha : CTyped weights Γ (.var i) cnum)
    (hb : CTyped weights Γ (.var j) cnum) :
    CTyped weights (.snoc (.snoc Γ cnum) (.app (mulAssocFamily i.succ j.succ) (.var 0)))
      (mulAssocStepBody i j) (.app (mulAssocFamily i.succ.succ j.succ.succ) (csuc (.var 1))) := by
  have a : CTyped weights (.snoc (.snoc Γ cnum) (.app (mulAssocFamily i.succ j.succ) (.var 0)))
      (.var i.succ.succ) cnum := CTyped.weaken (CTyped.weaken ha)
  have b : CTyped weights (.snoc (.snoc Γ cnum) (.app (mulAssocFamily i.succ j.succ) (.var 0)))
      (.var j.succ.succ) cnum := CTyped.weaken (CTyped.weaken hb)
  have k : CTyped weights (.snoc (.snoc Γ cnum) (.app (mulAssocFamily i.succ j.succ) (.var 0)))
      (.var 1) cnum := .var 1
  have hypothesis : CTyped weights
      (.snoc (.snoc Γ cnum) (.app (mulAssocFamily i.succ j.succ) (.var 0))) (.var 0)
      (.id cnum (cmul (cmul (.var i.succ.succ) (.var j.succ.succ)) (.var 1))
        (cmul (.var i.succ.succ) (cmul (.var j.succ.succ) (.var 1)))) :=
    .conv (.var 0) (mulAssocFamily_at a b k) (uSort subW _)
  have carried := wCongAddRight (wMul a b) (wMul (wMul a b) k) (wMul a (wMul b k)) hypothesis
  have distributed := wMulAdd a (wMul b k) b
  have turned := tSym subW (tNum subW) (wMul a (tAdd subW (wMul b k) b))
    (tAdd subW (wMul a (wMul b k)) (wMul a b)) distributed
  have joined := tTrans subW (tNum subW) (tAdd subW (wMul (wMul a b) k) (wMul a b))
    (tAdd subW (wMul a (wMul b k)) (wMul a b)) (wMul a (tAdd subW (wMul b k) b)) carried turned
  have computed : CEqual weights
      (.snoc (.snoc Γ cnum) (.app (mulAssocFamily i.succ j.succ) (.var 0)))
      (.id cnum (cmul (cmul (.var i.succ.succ) (.var j.succ.succ)) (csuc (.var 1)))
        (cmul (.var i.succ.succ) (cmul (.var j.succ.succ) (csuc (.var 1)))))
      (.id cnum (cadd (cmul (cmul (.var i.succ.succ) (.var j.succ.succ)) (.var 1))
          (cmul (.var i.succ.succ) (.var j.succ.succ)))
        (cmul (.var i.succ.succ) (cadd (cmul (.var j.succ.succ) (.var 1)) (.var j.succ.succ))))
            cU0 :=
    .idCong (.refl (tNum subW)) (uSort subW _) (wMulSuc (wMul a b) k)
      (eMul (.refl a) (wMulSuc b k))
  exact .conv joined
    (.symm (.trans (mulAssocFamily_at a b (tSuc subW k)) computed)) (uSort subW _)

abbrev mulAssocStep (i j : Fin n) : CTm Tower.Head n :=
  .lam cnum (.lam (.app (mulAssocFamily i.succ j.succ) (.var 0)) (mulAssocStepBody i j))

theorem mulAssocStep_typed {i j : Fin n} (ha : CTyped weights Γ (.var i) cnum)
    (hb : CTyped weights Γ (.var j) cnum) :
    CTyped weights Γ (mulAssocStep i j)
      (.pi cnum (.pi (.app (mulAssocFamily i.succ j.succ) (.var 0))
        (.app (mulAssocFamily i.succ.succ j.succ.succ) (csuc (.var 1))))) := by
  have first : CTyped weights (.snoc Γ cnum) (.var i.succ) cnum := CTyped.weaken ha
  have second : CTyped weights (.snoc Γ cnum) (.var j.succ) cnum := CTyped.weaken hb
  have hypType :
      CTyped weights (.snoc Γ cnum) (.app (mulAssocFamily i.succ j.succ) (.var 0)) cU0 :=
    .appElim (B := cU0) (mulAssocFamily_typed first second) (.var 0)
  have goalType : CTyped weights
      (.snoc (.snoc Γ cnum) (.app (mulAssocFamily i.succ j.succ) (.var 0)))
      (.app (mulAssocFamily i.succ.succ j.succ.succ) (csuc (.var 1))) cU0 :=
    .appElim (B := cU0) (mulAssocFamily_typed (CTyped.weaken first) (CTyped.weaken second))
      (tSuc subW (.var 1))
  have inner := tPi subW hypType goalType
  exact .lamIntro (tNum subW) (uSort subW _) (tPi subW (tNum subW) inner) (uSort subW _)
    (.lamIntro hypType (uSort subW _) inner (uSort subW _) (mulAssocStepBody_typed ha hb))

abbrev mulAssocProof : CTm Tower.Head n :=
  .lam cnum (.lam cnum (.lam cnum
    (cRecApp (mulAssocFamily 2 1) (.refl czero) (mulAssocStep 2 1) (.var 0))))

/-- The statement of associativity of the product. -/
abbrev mulAssocStatement : CTm Tower.Head n :=
  .pi cnum (.pi cnum (.pi cnum (.id cnum (cmul (cmul (.var 2) (.var 1)) (.var 0))
    (cmul (.var 2) (cmul (.var 1) (.var 0))))))

/-- **The product of numbers is associative**, by induction on the last factor. -/
theorem mul_assoc_identity : CTyped weights Γ mulAssocProof mulAssocStatement := by
  have first : CTyped weights (.snoc (.snoc (.snoc Γ cnum) cnum) cnum) (.var 2) cnum := .var 2
  have second : CTyped weights (.snoc (.snoc (.snoc Γ cnum) cnum) cnum) (.var 1) cnum := .var 1
  have body : CTyped weights (.snoc (.snoc (.snoc Γ cnum) cnum) cnum)
      (cRecApp (mulAssocFamily 2 1) (.refl czero) (mulAssocStep 2 1) (.var 0))
      (.id cnum (cmul (cmul (.var 2) (.var 1)) (.var 0)) (cmul (.var 2) (cmul (.var 1)
          (.var 0)))) :=
    .conv (tRec subW (mulAssocFamily_typed first second) (mulAssocBase_typed first second)
      (mulAssocStep_typed first second) (.var 0)) (mulAssocFamily_at first second (.var 0))
      (uSort subW _)
  have inner3 : CTyped weights (.snoc (.snoc Γ cnum) cnum)
      (.pi cnum (.id cnum (cmul (cmul (.var 2) (.var 1)) (.var 0))
        (cmul (.var 2) (cmul (.var 1) (.var 0))))) cU0 :=
    tPi subW (tNum subW) (tId subW (tNum subW) (wMul (wMul (.var 2) (.var 1)) (.var 0))
      (wMul (.var 2) (wMul (.var 1) (.var 0))))
  have inner2 : CTyped weights (.snoc Γ cnum)
      (.pi cnum (.pi cnum (.id cnum (cmul (cmul (.var 2) (.var 1)) (.var 0))
        (cmul (.var 2) (cmul (.var 1) (.var 0)))))) cU0 :=
    tPi subW (tNum subW) inner3
  exact .lamIntro (tNum subW) (uSort subW _) (tPi subW (tNum subW) inner2) (uSort subW _)
    (.lamIntro (tNum subW) (uSort subW _) inner2 (uSort subW _)
      (.lamIntro (tNum subW) (uSort subW _) inner3 (uSort subW _) body))

end NumberLaws


/-! ## The laws of the product of evidence counts -/

section EvidenceLaws

variable {n : Nat} {Γ : CCtx Tower.Head n}

theorem wEvType : CTyped weights Γ cEvidence cU0 := tEvidenceType weightProgram_admissible (by
    member_tac)

theorem wEvidence {p q : CTm Tower.Head n} (hp : CTyped weights Γ p cnum) (hq : CTyped weights Γ q
    cnum) :
    CTyped weights Γ (cevidence p q) cEvidence :=
  tEvidence weightProgram_admissible (by member_tac) hp hq

theorem wPositive {e : CTm Tower.Head n} (he : CTyped weights Γ e cEvidence) :
    CTyped weights Γ (cpositive e) cnum :=
  tPositive weightProgram_admissible (by member_tac) he

theorem wNegative {e : CTm Tower.Head n} (he : CTyped weights Γ e cEvidence) :
    CTyped weights Γ (cnegative e) cnum :=
  tNegative weightProgram_admissible (by member_tac) he

theorem wTensor {e f : CTm Tower.Head n} (he : CTyped weights Γ e cEvidence)
    (hf : CTyped weights Γ f cEvidence) : CTyped weights Γ (ctensor e f) cEvidence :=
  tTensor weightProgram_admissible (by member_tac) he hf

theorem wUnit : CTyped weights Γ cunit cEvidence := wEvidence (tOne subW) (tOne subW)

/-- **The product of packets unfolds**, count by count. -/
theorem wTensorUnfold {e f : CTm Tower.Head n} (he : CTyped weights Γ e cEvidence)
    (hf : CTyped weights Γ f cEvidence) :
    CEqual weights Γ (ctensor e f)
      (cevidence (cmul (cpositive e) (cpositive f)) (cmul (cnegative e) (cnegative f))) cEvidence :=
  definition_equation_holds (D := .explicit tensorDef) (by member_tac) (e := tensorEquation)
    (by rw [show Definition.equations (.explicit tensorDef) = tensorDef.equations from rfl,
      tensorDef_equations]; exact List.mem_singleton_self _)
    (fun i => [f, e].getD i.val e)
    (fun j => match j with
      | ⟨0, _⟩ => hf
      | ⟨1, _⟩ => he)
    (wTensor he hf)
    (wEvidence (wMul (wPositive he) (wPositive hf)) (wMul (wNegative he) (wNegative hf)))

theorem wPositiveTensor {e f : CTm Tower.Head n} (he : CTyped weights Γ e cEvidence)
    (hf : CTyped weights Γ f cEvidence) :
    CEqual weights Γ (cpositive (ctensor e f)) (cmul (cpositive e) (cpositive f)) cnum :=
  .trans (.appCong (B := cnum)
      (.refl (weightProgram_admissible.definition_typed ConvRules.objectLevels
        (D := .recursive positiveDef) (by member_tac))) (wTensorUnfold he hf))
    (ePositive weightProgram_admissible (by member_tac) (by member_tac)
      (wMul (wPositive he) (wPositive hf)) (wMul (wNegative he) (wNegative hf)))

theorem wNegativeTensor {e f : CTm Tower.Head n} (he : CTyped weights Γ e cEvidence)
    (hf : CTyped weights Γ f cEvidence) :
    CEqual weights Γ (cnegative (ctensor e f)) (cmul (cnegative e) (cnegative f)) cnum :=
  .trans (.appCong (B := cnum)
      (.refl (weightProgram_admissible.definition_typed ConvRules.objectLevels
        (D := .recursive negativeDef) (by member_tac))) (wTensorUnfold he hf))
    (eNegative weightProgram_admissible (by member_tac) (by member_tac)
      (wMul (wPositive he) (wPositive hf)) (wMul (wNegative he) (wNegative hf)))

/-- **Every packet is the packet of its counts**: the declared proof by induction. -/
theorem wEta {e : CTm Tower.Head n} (he : CTyped weights Γ e cEvidence) :
    CTyped weights Γ (.app (.const evidenceEtaN) e) (etaAt e) :=
  .appElim (B := etaAt (.var 0))
    (weightProgram_admissible.definition_typed ConvRules.objectLevels
      (D := .recursive evidenceEtaDef) (by member_tac)) he

/-- The packet of a count with a fixed negative count. -/
abbrev withNegative (y : CTm Tower.Head n) : CTm Tower.Head n :=
  .lam cnum (cevidence (.var 0) (y.rename wk))

/-- **Identity proofs of the two counts give an identity proof of the packets.** -/
abbrev evidenceCongOf (x x' y y' p q : CTm Tower.Head n) : CTm Tower.Head n :=
  transOf cEvidence (cevidence x y) (cevidence x' y) (cevidence x' y')
    (congOf cnum cEvidence (withNegative y) x x' p)
    (congOf cnum cEvidence (.app (.const evidenceN) x') y y' q)

theorem wEvidenceCong {x x' y y' p q : CTm Tower.Head n} (hx : CTyped weights Γ x cnum)
    (hx' : CTyped weights Γ x' cnum) (hy : CTyped weights Γ y cnum)
    (hy' : CTyped weights Γ y' cnum) (hp : CTyped weights Γ p (.id cnum x x'))
    (hq : CTyped weights Γ q (.id cnum y y')) :
    CTyped weights Γ (evidenceCongOf x x' y y' p q)
      (.id cEvidence (cevidence x y) (cevidence x' y')) := by
  have body : CTyped weights (.snoc Γ cnum) (cevidence (.var 0) (y.rename wk)) cEvidence :=
    wEvidence (.var 0) (CTyped.weaken hy)
  have fnType : CTyped weights Γ (.pi cnum cEvidence) cU0 := tPi subW (tNum subW) wEvType
  have fn : CTyped weights Γ (withNegative y) (.pi cnum (cEvidence.rename wk)) :=
    .lamIntro (tNum subW) (uSort subW _) fnType (uSort subW _) body
  have beta : ∀ {u : CTm Tower.Head n}, CTyped weights Γ u cnum →
      CEqual weights Γ (.app (withNegative y) u) (cevidence u y) cEvidence := by
    intro u hu
    have reduced := CDerivable.betaPi (A := cnum) (B := cEvidence)
      (body := cevidence (.var 0) (y.rename wk)) (a := u) fnType (uSort subW _) body hu
    have same : CTm.inst0 u (cevidence (.var 0) (y.rename wk) : CTm Tower.Head (n + 1)) =
        cevidence u y := by
      show cevidence u (CTm.inst0 u (y.rename wk)) = cevidence u y
      rw [CTm.inst0_rename_wk]
    rw [same] at reduced
    exact reduced
  have first : CTyped weights Γ (congOf cnum cEvidence (withNegative y) x x' p)
      (.id cEvidence (cevidence x y) (cevidence x' y)) :=
    .conv (tCong subW (tNum subW) wEvType fn hx hx' hp)
      (.idCong (.refl wEvType) (uSort subW _) (beta hx) (beta hx')) (uSort subW _)
  have partialCtor : CTyped weights Γ (.app (.const evidenceN) x') (.pi cnum (cEvidence.rename
      wk)) :=
    .appElim (B := .pi cnum cEvidence) (tEvidenceCtor weightProgram_admissible (by member_tac)) hx'
  have second : CTyped weights Γ (congOf cnum cEvidence (.app (.const evidenceN) x') y y' q)
      (.id cEvidence (cevidence x' y) (cevidence x' y')) :=
    tCong subW (tNum subW) wEvType partialCtor hy hy' hq
  exact tTrans subW wEvType (wEvidence hx hy) (wEvidence hx' hy) (wEvidence hx' hy') first second

/-- Associativity of the product of numbers at three variables. -/
theorem mulAssoc_atVars :
    CTyped weights (CCtx.snoc (.snoc (.snoc .nil cnum) cnum) cnum : CCtx Tower.Head 3)
      (.app (.app (.app mulAssocProof (.var 2)) (.var 1)) (.var 0))
      (.id cnum (cmul (cmul (.var 2) (.var 1)) (.var 0)) (cmul (.var 2) (cmul (.var 1)
          (.var 0)))) :=
  have first : CTyped weights (CCtx.snoc (.snoc (.snoc .nil cnum) cnum) cnum : CCtx Tower.Head 3)
      (.app mulAssocProof (.var 2))
      (.pi cnum (.pi cnum (.id cnum (cmul (cmul (.var 4) (.var 1)) (.var 0))
        (cmul (.var 4) (cmul (.var 1) (.var 0)))))) :=
    .appElim (B := .pi cnum (.pi cnum (.id cnum (cmul (cmul (.var 2) (.var 1)) (.var 0))
      (cmul (.var 2) (cmul (.var 1) (.var 0)))))) mul_assoc_identity (.var 2)
  have second : CTyped weights (CCtx.snoc (.snoc (.snoc .nil cnum) cnum) cnum : CCtx Tower.Head 3)
      (.app (.app mulAssocProof (.var 2)) (.var 1))
      (.pi cnum (.id cnum (cmul (cmul (.var 3) (.var 2)) (.var 0))
        (cmul (.var 3) (cmul (.var 2) (.var 0))))) :=
    .appElim (B := .pi cnum (.id cnum (cmul (cmul (.var 4) (.var 1)) (.var 0))
      (cmul (.var 4) (cmul (.var 1) (.var 0))))) first (.var 1)
  .appElim (B := .id cnum (cmul (cmul (.var 3) (.var 2)) (.var 0))
    (cmul (.var 3) (cmul (.var 2) (.var 0)))) second (.var 0)

/-- The instance of the associativity proof at three numbers, as a substitution instance of
the proof at three variables. -/
abbrev mulAssocAt (x y z : CTm Tower.Head n) : CTm Tower.Head n :=
  CTm.subst (fun i => [z, y, x].getD i.val x)
    (.app (.app (.app mulAssocProof (.var 2)) (.var 1)) (.var 0) : CTm Tower.Head 3)

/-- An instance of the associativity of the product of numbers. -/
theorem wMulAssoc {x y z : CTm Tower.Head n} (hx : CTyped weights Γ x cnum)
    (hy : CTyped weights Γ y cnum) (hz : CTyped weights Γ z cnum) :
    CTyped weights Γ (mulAssocAt x y z) (.id cnum (cmul (cmul x y) z) (cmul x (cmul y z))) :=
  CTyped.substitute mulAssoc_atVars (σ := fun i => [z, y, x].getD i.val x)
    (fun j => match j with
      | ⟨0, _⟩ => hz
      | ⟨1, _⟩ => hy
      | ⟨2, _⟩ => hx)

/-- The proof of associativity of the product of packets, over three packets. -/
abbrev tensorAssocBody : CTm Tower.Head 3 :=
  evidenceCongOf
    (cmul (cmul (cpositive (.var 2)) (cpositive (.var 1))) (cpositive (.var 0)))
    (cmul (cpositive (.var 2)) (cmul (cpositive (.var 1)) (cpositive (.var 0))))
    (cmul (cmul (cnegative (.var 2)) (cnegative (.var 1))) (cnegative (.var 0)))
    (cmul (cnegative (.var 2)) (cmul (cnegative (.var 1)) (cnegative (.var 0))))
    (mulAssocAt (cpositive (.var 2)) (cpositive (.var 1)) (cpositive (.var 0)))
    (mulAssocAt (cnegative (.var 2)) (cnegative (.var 1)) (cnegative (.var 0)))

abbrev tensorAssocProof : CTm Tower.Head 0 :=
  .lam cEvidence (.lam cEvidence (.lam cEvidence tensorAssocBody))

/-- The statement of associativity of the product of packets. -/
abbrev tensorAssocStatement : CTm Tower.Head 0 :=
  .pi cEvidence (.pi cEvidence (.pi cEvidence
    (.id cEvidence (ctensor (ctensor (.var 2) (.var 1)) (.var 0))
      (ctensor (.var 2) (ctensor (.var 1) (.var 0))))))

/-- The body of the associativity proof of packets, over three packets. -/
theorem tensorAssocBody_typed :
    CTyped weights (CCtx.snoc (.snoc (.snoc .nil cEvidence) cEvidence) cEvidence : CCtx Tower.Head
        3)
      tensorAssocBody (.id cEvidence (ctensor (ctensor (.var 2) (.var 1)) (.var 0))
        (ctensor (.var 2) (ctensor (.var 1) (.var 0)))) := by
  have e : CTyped weights (CCtx.snoc (.snoc (.snoc .nil cEvidence) cEvidence) cEvidence : CCtx
      Tower.Head 3)
      (.var 2) cEvidence := .var 2
  have f : CTyped weights (CCtx.snoc (.snoc (.snoc .nil cEvidence) cEvidence) cEvidence : CCtx
      Tower.Head 3)
      (.var 1) cEvidence := .var 1
  have g : CTyped weights (CCtx.snoc (.snoc (.snoc .nil cEvidence) cEvidence) cEvidence : CCtx
      Tower.Head 3)
      (.var 0) cEvidence := .var 0
  have proof := wEvidenceCong
    (wMul (wMul (wPositive e) (wPositive f)) (wPositive g))
    (wMul (wPositive e) (wMul (wPositive f) (wPositive g)))
    (wMul (wMul (wNegative e) (wNegative f)) (wNegative g))
    (wMul (wNegative e) (wMul (wNegative f) (wNegative g)))
    (wMulAssoc (wPositive e) (wPositive f) (wPositive g))
    (wMulAssoc (wNegative e) (wNegative f) (wNegative g))
  have left : CEqual weights (CCtx.snoc (.snoc (.snoc .nil cEvidence) cEvidence) cEvidence : CCtx
      Tower.Head 3)
      (ctensor (ctensor (.var 2) (.var 1)) (.var 0))
      (cevidence (cmul (cmul (cpositive (.var 2)) (cpositive (.var 1))) (cpositive (.var 0)))
        (cmul (cmul (cnegative (.var 2)) (cnegative (.var 1))) (cnegative (.var 0)))) cEvidence :=
    .trans (wTensorUnfold (wTensor e f) g)
      (eEvidence weightProgram_admissible (by member_tac)
        (eMul (wPositiveTensor e f) (.refl (wPositive g)))
        (eMul (wNegativeTensor e f) (.refl (wNegative g))))
  have right : CEqual weights (CCtx.snoc (.snoc (.snoc .nil cEvidence) cEvidence) cEvidence : CCtx
      Tower.Head 3)
      (ctensor (.var 2) (ctensor (.var 1) (.var 0)))
      (cevidence (cmul (cpositive (.var 2)) (cmul (cpositive (.var 1)) (cpositive (.var 0))))
        (cmul (cnegative (.var 2)) (cmul (cnegative (.var 1)) (cnegative (.var 0))))) cEvidence :=
    .trans (wTensorUnfold e (wTensor f g))
      (eEvidence weightProgram_admissible (by member_tac)
        (eMul (.refl (wPositive e)) (wPositiveTensor f g))
        (eMul (.refl (wNegative e)) (wNegativeTensor f g)))
  exact .conv proof (.symm (.idCong (.refl wEvType) (uSort subW _) left right)) (uSort subW _)

/-- **The product of evidence packets is associative**: both sides compute count by count,
and the two counts agree by associativity of the product of numbers. -/
theorem tensor_assoc_identity : CTyped weights .nil tensorAssocProof tensorAssocStatement := by
  have inner3 : CTyped weights (CCtx.snoc (.snoc .nil cEvidence) cEvidence : CCtx Tower.Head 2)
      (.pi cEvidence (.id cEvidence (ctensor (ctensor (.var 2) (.var 1)) (.var 0))
        (ctensor (.var 2) (ctensor (.var 1) (.var 0))))) cU0 :=
    tPi subW wEvType (tId subW wEvType (wTensor (wTensor (.var 2) (.var 1)) (.var 0))
      (wTensor (.var 2) (wTensor (.var 1) (.var 0))))
  have inner2 : CTyped weights (CCtx.snoc .nil cEvidence : CCtx Tower.Head 1)
      (.pi cEvidence (.pi cEvidence (.id cEvidence (ctensor (ctensor (.var 2) (.var 1)) (.var 0))
        (ctensor (.var 2) (ctensor (.var 1) (.var 0)))))) cU0 :=
    tPi subW wEvType inner3
  exact .lamIntro wEvType (uSort subW _) (tPi subW wEvType inner2) (uSort subW _)
    (.lamIntro wEvType (uSort subW _) inner2 (uSort subW _)
      (.lamIntro wEvType (uSort subW _) inner3 (uSort subW _) tensorAssocBody_typed))

/-- The proof of the left unit law of packets, over a packet. -/
abbrev tensorOneLeftBody : CTm Tower.Head 1 :=
  transOf cEvidence (cevidence (cmul cone (cpositive (.var 0))) (cmul cone (cnegative (.var 0))))
    (cevidence (cpositive (.var 0)) (cnegative (.var 0))) (.var 0)
    (evidenceCongOf (cmul cone (cpositive (.var 0))) (cpositive (.var 0))
      (cmul cone (cnegative (.var 0))) (cnegative (.var 0))
      (.app mulOneLeftProof (cpositive (.var 0))) (.app mulOneLeftProof (cnegative (.var 0))))
    (.app (.const evidenceEtaN) (.var 0))

abbrev tensorOneLeftProof : CTm Tower.Head 0 := .lam cEvidence tensorOneLeftBody

abbrev tensorOneLeftStatement : CTm Tower.Head 0 :=
  .pi cEvidence (.id cEvidence (ctensor cunit (.var 0)) (.var 0))

/-- **The unit packet `(evidence 1 1)` is a left unit**: count by count, then every packet is
the packet of its counts. -/
theorem tensor_one_left_identity : CTyped weights .nil tensorOneLeftProof tensorOneLeftStatement :=
    by
  have e : CTyped weights (CCtx.snoc .nil cEvidence : CCtx Tower.Head 1) (.var 0) cEvidence := .var
      0
  have onePositive : CTyped weights (CCtx.snoc .nil cEvidence : CCtx Tower.Head 1)
      (.app mulOneLeftProof (cpositive (.var 0))) (.id cnum (cmul cone (cpositive (.var 0)))
          (cpositive (.var 0))) :=
    .appElim (B := .id cnum (cmul cone (.var 0)) (.var 0)) mul_one_left_identity (wPositive e)
  have oneNegative : CTyped weights (CCtx.snoc .nil cEvidence : CCtx Tower.Head 1)
      (.app mulOneLeftProof (cnegative (.var 0))) (.id cnum (cmul cone (cnegative (.var 0)))
          (cnegative (.var 0))) :=
    .appElim (B := .id cnum (cmul cone (.var 0)) (.var 0)) mul_one_left_identity (wNegative e)
  have counts := wEvidenceCong (wMul (tOne subW) (wPositive e)) (wPositive e)
    (wMul (tOne subW) (wNegative e)) (wNegative e) onePositive oneNegative
  have joined := tTrans subW wEvType
    (wEvidence (wMul (tOne subW) (wPositive e)) (wMul (tOne subW) (wNegative e)))
    (wEvidence (wPositive e) (wNegative e)) e counts (wEta e)
  have unitCounts : CEqual weights (CCtx.snoc .nil cEvidence : CCtx Tower.Head 1)
      (ctensor cunit (.var 0))
      (cevidence (cmul cone (cpositive (.var 0))) (cmul cone (cnegative (.var 0)))) cEvidence :=
    .trans (wTensorUnfold wUnit e)
      (eEvidence weightProgram_admissible (by member_tac)
        (eMul (ePositive weightProgram_admissible (by member_tac) (by member_tac)
          (tOne subW) (tOne subW)) (.refl (wPositive e)))
        (eMul (eNegative weightProgram_admissible (by member_tac) (by member_tac)
          (tOne subW) (tOne subW)) (.refl (wNegative e))))
  have stated : CTyped weights (CCtx.snoc .nil cEvidence : CCtx Tower.Head 1) tensorOneLeftBody
      (.id cEvidence (ctensor cunit (.var 0)) (.var 0)) :=
    .conv joined (.symm (.idCong (.refl wEvType) (uSort subW _) unitCounts (.refl e))) (uSort subW
        _)
  exact .lamIntro wEvType (uSort subW _) (tPi subW wEvType (tId subW wEvType (wTensor wUnit e) e))
    (uSort subW _) stated

/-- The proof of the right unit law of packets, over a packet. -/
abbrev tensorOneRightBody : CTm Tower.Head 1 :=
  transOf cEvidence (cevidence (cmul (cpositive (.var 0)) cone) (cmul (cnegative (.var 0)) cone))
    (cevidence (cpositive (.var 0)) (cnegative (.var 0))) (.var 0)
    (evidenceCongOf (cmul (cpositive (.var 0)) cone) (cpositive (.var 0))
      (cmul (cnegative (.var 0)) cone) (cnegative (.var 0))
      (.app mulOneRightProof (cpositive (.var 0))) (.app mulOneRightProof (cnegative (.var 0))))
    (.app (.const evidenceEtaN) (.var 0))

abbrev tensorOneRightProof : CTm Tower.Head 0 := .lam cEvidence tensorOneRightBody

abbrev tensorOneRightStatement : CTm Tower.Head 0 :=
  .pi cEvidence (.id cEvidence (ctensor (.var 0) cunit) (.var 0))

/-- **The unit packet is a right unit.** -/
theorem tensor_one_right_identity :
    CTyped weights .nil tensorOneRightProof tensorOneRightStatement := by
  have e : CTyped weights (CCtx.snoc .nil cEvidence : CCtx Tower.Head 1) (.var 0) cEvidence := .var
      0
  have onePositive : CTyped weights (CCtx.snoc .nil cEvidence : CCtx Tower.Head 1)
      (.app mulOneRightProof (cpositive (.var 0))) (.id cnum (cmul (cpositive (.var 0)) cone)
          (cpositive (.var 0))) :=
    .appElim (B := .id cnum (cmul (.var 0) cone) (.var 0)) mul_one_right_identity (wPositive e)
  have oneNegative : CTyped weights (CCtx.snoc .nil cEvidence : CCtx Tower.Head 1)
      (.app mulOneRightProof (cnegative (.var 0))) (.id cnum (cmul (cnegative (.var 0)) cone)
          (cnegative (.var 0))) :=
    .appElim (B := .id cnum (cmul (.var 0) cone) (.var 0)) mul_one_right_identity (wNegative e)
  have counts := wEvidenceCong (wMul (wPositive e) (tOne subW)) (wPositive e)
    (wMul (wNegative e) (tOne subW)) (wNegative e) onePositive oneNegative
  have joined := tTrans subW wEvType
    (wEvidence (wMul (wPositive e) (tOne subW)) (wMul (wNegative e) (tOne subW)))
    (wEvidence (wPositive e) (wNegative e)) e counts (wEta e)
  have unitCounts : CEqual weights (CCtx.snoc .nil cEvidence : CCtx Tower.Head 1)
      (ctensor (.var 0) cunit)
      (cevidence (cmul (cpositive (.var 0)) cone) (cmul (cnegative (.var 0)) cone)) cEvidence :=
    .trans (wTensorUnfold e wUnit)
      (eEvidence weightProgram_admissible (by member_tac)
        (eMul (.refl (wPositive e)) (ePositive weightProgram_admissible (by member_tac)
          (by member_tac) (tOne subW) (tOne subW)))
        (eMul (.refl (wNegative e)) (eNegative weightProgram_admissible (by member_tac)
          (by member_tac) (tOne subW) (tOne subW))))
  have stated : CTyped weights (CCtx.snoc .nil cEvidence : CCtx Tower.Head 1) tensorOneRightBody
      (.id cEvidence (ctensor (.var 0) cunit) (.var 0)) :=
    .conv joined (.symm (.idCong (.refl wEvType) (uSort subW _) unitCounts (.refl e))) (uSort subW
        _)
  exact .lamIntro wEvType (uSort subW _) (tPi subW wEvType (tId subW wEvType (wTensor e wUnit) e))
    (uSort subW _) stated

end EvidenceLaws


/-! ## The value-to-weight maps -/

section WeightMaps

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- **The weight of a number read as a number is a typed constant**, `num → num`. -/
theorem numberWeight_typed : CTyped weights Γ (.const numberWeightN) (.pi cnum cnum) :=
  weightProgram_admissible.definition_typed ConvRules.objectLevels
    (D := .explicit numberWeightDef) (by member_tac)

/-- **The weight of a number read as an evidence count is a typed constant**,
`num → Evidence`. -/
theorem countWeight_typed : CTyped weights Γ (.const countWeightN) (.pi cnum cEvidence) :=
  weightProgram_admissible.definition_typed ConvRules.objectLevels
    (D := .explicit countWeightDef) (by member_tac)

/-- `number-weight x ≡ x`. -/
theorem numberWeight_rule {x : CTm Tower.Head n} (hx : CTyped weights Γ x cnum) :
    CEqual weights Γ (.app (.const numberWeightN) x) x cnum :=
  definition_equation_holds (D := .explicit numberWeightDef) (by member_tac)
    (e := numberWeightEquation)
    (by rw [show Definition.equations (.explicit numberWeightDef) = numberWeightDef.equations
      from rfl, numberWeightDef_equations]; exact List.mem_singleton_self _)
    (fun _ => x) (fun j => match j with | ⟨0, _⟩ => hx)
    (.appElim (B := cnum) numberWeight_typed hx) hx

/-- `count-weight n ≡ evidence n 1`. -/
theorem countWeight_rule {x : CTm Tower.Head n} (hx : CTyped weights Γ x cnum) :
    CEqual weights Γ (.app (.const countWeightN) x) (cevidence x cone) cEvidence :=
  definition_equation_holds (D := .explicit countWeightDef) (by member_tac)
    (e := countWeightEquation)
    (by rw [show Definition.equations (.explicit countWeightDef) = countWeightDef.equations
      from rfl, countWeightDef_equations]; exact List.mem_singleton_self _)
    (fun _ => x) (fun j => match j with | ⟨0, _⟩ => hx)
    (.appElim (B := cEvidence) countWeight_typed hx) (wEvidence hx (tOne subW))

end WeightMaps

/-! ## Numerals compute -/

section Numerals

/-- A numeral is a number. -/
theorem wNumeral {n : Nat} {Γ : CCtx Tower.Head n} :
    ∀ k : Nat, CTyped weights Γ (cnumeral k) cnum
  | 0 => tZero subW
  | k + 1 => tSuc subW (wNumeral k)

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- The sum of two numerals is the numeral of their sum, in the judgment. -/
theorem eAddNumeral (a : Nat) :
    ∀ b : Nat, CEqual weights Γ (cadd (cnumeral a) (cnumeral b)) (cnumeral (a + b)) cnum
  | 0 => eAddZero subW (wNumeral a)
  | b + 1 => .trans (eAddSuc subW (wNumeral a) (wNumeral b)) (eSuc subW (eAddNumeral a b))

/-- The product of two numerals is the numeral of their product, in the judgment. -/
theorem eMulNumeral (a : Nat) :
    ∀ b : Nat, CEqual weights Γ (cmul (cnumeral a) (cnumeral b)) (cnumeral (a * b)) cnum
  | 0 => wMulZero (wNumeral a)
  | b + 1 => .trans (wMulSuc (wNumeral a) (wNumeral b))
      (.trans (eAdd subW (eMulNumeral a b) (.refl (wNumeral a))) (eAddNumeral (a * b) a))

/-- Positive example: **the coefficient of an occurrence of the shared pair is computed in the
package**, the coin's weight `3` times the identity's weight `number-weight 2`. -/
theorem coefficient_six :
    CEqual weights Γ (cmul (cnumeral 3) (.app (.const numberWeightN) (cnumeral 2))) (cnumeral 6)
      cnum :=
  .trans (eMul (.refl (wNumeral 3)) (numberWeight_rule (wNumeral 2))) (eMulNumeral 3 2)

/-- Positive example: **over evidence counts**, the packet `(evidence 3 1)` times
`count-weight 2` is `(evidence 6 1)`. -/
theorem packet_six :
    CEqual weights Γ (ctensor (cevidence (cnumeral 3) (cnumeral 1)) (.app (.const countWeightN)
        (cnumeral 2)))
      (cevidence (cnumeral 6) (cnumeral 1)) cEvidence := by
  have three : CTyped weights Γ (cevidence (cnumeral 3) (cnumeral 1)) cEvidence :=
    wEvidence (wNumeral 3) (wNumeral 1)
  have weighted : CTyped weights Γ (.app (.const countWeightN) (cnumeral 2)) cEvidence :=
    .appElim (B := cEvidence) countWeight_typed (wNumeral 2)
  have two : CEqual weights Γ (.app (.const countWeightN) (cnumeral 2))
      (cevidence (cnumeral 2) (cnumeral 1)) cEvidence := countWeight_rule (wNumeral 2)
  have positiveTwo : CEqual weights Γ (cpositive (.app (.const countWeightN) (cnumeral 2)))
      (cnumeral 2) cnum :=
    .trans (.appCong (B := cnum)
        (.refl (weightProgram_admissible.definition_typed ConvRules.objectLevels
          (D := .recursive positiveDef) (by member_tac))) two)
      (ePositive weightProgram_admissible (by member_tac) (by member_tac) (wNumeral 2) (wNumeral 1))
  have negativeTwo : CEqual weights Γ (cnegative (.app (.const countWeightN) (cnumeral 2)))
      (cnumeral 1) cnum :=
    .trans (.appCong (B := cnum)
        (.refl (weightProgram_admissible.definition_typed ConvRules.objectLevels
          (D := .recursive negativeDef) (by member_tac))) two)
      (eNegative weightProgram_admissible (by member_tac) (by member_tac) (wNumeral 2) (wNumeral 1))
  exact .trans (wTensorUnfold three weighted)
    (eEvidence weightProgram_admissible (by member_tac)
      (.trans (eMul (ePositive weightProgram_admissible (by member_tac) (by member_tac)
        (wNumeral 3) (wNumeral 1)) positiveTwo) (eMulNumeral 3 2))
      (.trans (eMul (eNegative weightProgram_admissible (by member_tac) (by member_tac)
        (wNumeral 3) (wNumeral 1)) negativeTwo) (eMulNumeral 1 1)))

end Numerals

/-! ## The set model -/

section Model

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetTraceProofDecoding (mem_truthCode)

universe u

variable (h : CofinalInaccessibles.{u})

/-- **The weight package has a set model**, relative to `CofinalInaccessibles`, by the
criterion for admissible lists of declarations over the object package. -/
theorem weights_model :
    SetModel (objHeads h) (objectDeclarationsConsts h weightProgram) weights :=
  objectDeclarations_model h weightProgram_admissible

include h in
/-- **Consistency**: no closed term of the weight package has the type `Π (X : U₀). X`. -/
theorem weights_consistent (t : CTm Tower.Head 0) : ¬ CTyped weights .nil t emptyType :=
  objectDeclarations_consistent h weightProgram_admissible t

/-- In the model the product of numbers is associative, at every closed number of the
judgment. -/
theorem mul_assoc_value {a b c : CTm Tower.Head 0} (ha : CTyped weights .nil a cnum)
    (hb : CTyped weights .nil b cnum) (hc : CTyped weights .nil c cnum) :
    ev (objHeads h) (objectDeclarationsConsts h weightProgram) (cmul (cmul a b) c) Fin.elim0 =
      ev (objHeads h) (objectDeclarationsConsts h weightProgram) (cmul a (cmul b c)) Fin.elim0 :=
  ((mem_truthCode _ _).mp (objectDeclarations_sound h weightProgram_admissible
    (wMulAssoc ha hb hc) Fin.elim0 (sat_nil _ _ _))).2

/-- In the model the product of packets is associative, at every closed packet. -/
theorem tensor_assoc_value {e f g : CTm Tower.Head 0} (he : CTyped weights .nil e cEvidence)
    (hf : CTyped weights .nil f cEvidence) (hg : CTyped weights .nil g cEvidence) :
    ev (objHeads h) (objectDeclarationsConsts h weightProgram) (ctensor (ctensor e f) g) Fin.elim0 =
      ev (objHeads h) (objectDeclarationsConsts h weightProgram) (ctensor e (ctensor f g))
          Fin.elim0 := by
  have proof : CTyped weights .nil (CTm.subst (fun i => [g, f, e].getD i.val e) tensorAssocBody)
      (.id cEvidence (ctensor (ctensor e f) g) (ctensor e (ctensor f g))) :=
    CTyped.substitute tensorAssocBody_typed (σ := fun i => [g, f, e].getD i.val e)
      (fun j => match j with
        | ⟨0, _⟩ => hg
        | ⟨1, _⟩ => hf
        | ⟨2, _⟩ => he)
  exact ((mem_truthCode _ _).mp (objectDeclarations_sound h weightProgram_admissible proof
    Fin.elim0 (sat_nil _ _ _))).2

include h in
/-- Negative example: **the weight map of numbers is not a map to Boolean weights.** A
number used as a Boolean weight is ill-typed: if `number-weight` had the type
`num → Boolean`, its value at zero, which is zero, would be a Boolean, and in the model zero
is the empty set while every Boolean is a constructor value. -/
theorem numberWeight_not_boolean : ¬ CTyped weights .nil (.const numberWeightN) (.pi cnum
    cBoolean) := by
  intro typed
  have applied : CTyped weights .nil (.app (.const numberWeightN) czero) cBoolean :=
    .appElim (B := cBoolean) typed (tZero subW)
  have member := objectDeclarations_sound h weightProgram_admissible applied Fin.elim0 (sat_nil _ _
      _)
  have same := (objectDeclarations_sound h weightProgram_admissible
    (numberWeight_rule (Γ := .nil) (tZero subW)) Fin.elim0 (sat_nil _ _ _)).1
  rw [same] at member
  have reading := declarations_reading (heads := objHeads h) (base := objectSetConsts h)
    objectChurch weightProgram weightProgram_admissible booleanDecl (by member_tac)
    (objectDeclarationsConsts h weightProgram) fun _ _ => rfl
  have zeroValue : ev (objHeads h) (objectDeclarationsConsts h weightProgram) (czero : CTm
      Tower.Head 0)
      Fin.elim0 = ∅ := by
    show objectDeclarationsConsts h weightProgram zeroN = ∅
    rw [show objectDeclarationsConsts h weightProgram zeroN = objectSetConsts h zeroN from
      declarationsConsts_base objectChurch
        (objectChurch_constantType_ne_none (by decide)) weightProgram weightProgram_admissible,
      setConst_zero]
    rfl
  rw [zeroValue] at member
  change (∅ : ZFSet.{u}) ∈ objectDeclarationsConsts h weightProgram booleanDecl.type at member
  rw [reading.type] at member
  obtain ⟨_, c, args, _, _, value⟩ := ZFSetInductive.exists_inversion member
  exact ZFSetInductive.constructorValue_ne_empty c.tag args value

end Model


/-! ## Raw terms of the weight package and their formation-sensitive typing -/

/-- The rules of the weight package, read without annotations. -/
abbrev weightRules : Rules Tower.Head := rulesWith objectRules weightProgram

section Raw

variable {n : Nat} {Γ : Ctx Tower.Head n}

abbrev rNum : Tm Tower.Head n := .const numN
abbrev rNumberPair : Tm Tower.Head n := .const numberPairN
abbrev rEvidenceType : Tm Tower.Head n := .const evidenceTypeN
abbrev rPair (a b : Tm Tower.Head n) : Tm Tower.Head n := .app (.app (.const pairCtorN) a) b
abbrev rEvidence (p q : Tm Tower.Head n) : Tm Tower.Head n := .app (.app (.const evidenceN) p) q

/-- The numeral `k`, as a raw term. -/
def rNumeral : Nat → Tm Tower.Head n
  | 0 => .const zeroN
  | k + 1 => .app (.const sucN) (rNumeral k)

theorem fNum : FormationSensitive.Typing weightRules Γ rNum (.head (.sort Tower.zero)) :=
  .const (type := (Tm.head (LevelTower.Head.sort Tower.zero) : Tm Tower.Head 0)) (by decide)
    (.headType (LevelTower.HeadTyping.sort _)) (LevelTower.IsUniverse.sort _)

theorem fNumberPair :
    FormationSensitive.Typing weightRules Γ rNumberPair (.head (.sort Tower.zero)) :=
  .const (type := (Tm.head (LevelTower.Head.sort Tower.zero) : Tm Tower.Head 0)) (by decide)
    (.headType (LevelTower.HeadTyping.sort _)) (LevelTower.IsUniverse.sort _)

theorem fEvidenceType :
    FormationSensitive.Typing weightRules Γ rEvidenceType (.head (.sort Tower.zero)) :=
  .const (type := (Tm.head (LevelTower.Head.sort Tower.zero) : Tm Tower.Head 0)) (by decide)
    (.headType (LevelTower.HeadTyping.sort _)) (LevelTower.IsUniverse.sort _)

/-- A function type between two types of the lowest universe. -/
theorem fArrow {A : Tm Tower.Head n} {B : Tm Tower.Head (n + 1)}
    (hA : FormationSensitive.Typing weightRules Γ A (.head (.sort Tower.zero)))
    (hB : FormationSensitive.Typing weightRules (.snoc Γ A) B (.head (.sort Tower.zero))) :
    FormationSensitive.Typing weightRules Γ (.pi A B) (.head (.sort Tower.zero)) :=
  .cumul (.piForm hA (LevelTower.IsUniverse.sort _) hB (LevelTower.IsUniverse.sort _)
    (LevelTower.Join.sorts _ _)) (fun valuation => by simp [LevelExpr.eval])

theorem fZero : FormationSensitive.Typing weightRules Γ (.const zeroN) rNum :=
  .const (type := rNum) (by decide) fNum (LevelTower.IsUniverse.sort _)

theorem fSucConst : FormationSensitive.Typing weightRules Γ (.const sucN) (.pi rNum rNum) :=
  .const (type := .pi rNum rNum) (by decide) (fArrow fNum fNum) (LevelTower.IsUniverse.sort _)

theorem fNumeral : ∀ k : Nat, FormationSensitive.Typing weightRules Γ (rNumeral k) rNum
  | 0 => fZero
  | k + 1 => .appElim (B := rNum) fSucConst (fNumeral k)

theorem fPairCtor :
    FormationSensitive.Typing weightRules Γ (.const pairCtorN) (.pi rNum (.pi rNum rNumberPair)) :=
  .const (type := .pi rNum (.pi rNum rNumberPair)) (by decide)
    (fArrow fNum (fArrow fNum fNumberPair))
    (LevelTower.IsUniverse.sort _)

theorem fPair {a b : Tm Tower.Head n} (ha : FormationSensitive.Typing weightRules Γ a rNum)
    (hb : FormationSensitive.Typing weightRules Γ b rNum) :
    FormationSensitive.Typing weightRules Γ (rPair a b) rNumberPair :=
  .appElim (B := rNumberPair) (.appElim (B := .pi rNum rNumberPair) fPairCtor ha) hb

theorem fEvidenceCtor :
    FormationSensitive.Typing weightRules Γ (.const evidenceN) (.pi rNum (.pi rNum
        rEvidenceType)) :=
  .const (type := .pi rNum (.pi rNum rEvidenceType)) (by decide)
    (fArrow fNum (fArrow fNum fEvidenceType))
    (LevelTower.IsUniverse.sort _)

theorem fEvidence {p q : Tm Tower.Head n} (hp : FormationSensitive.Typing weightRules Γ p rNum)
    (hq : FormationSensitive.Typing weightRules Γ q rNum) :
    FormationSensitive.Typing weightRules Γ (rEvidence p q) rEvidenceType :=
  .appElim (B := rEvidenceType) (.appElim (B := .pi rNum rEvidenceType) fEvidenceCtor hp) hq

/-- **The number weight map, applied, is a number.** -/
theorem fNumberWeight {x : Tm Tower.Head n} (hx : FormationSensitive.Typing weightRules Γ x rNum) :
    FormationSensitive.Typing weightRules Γ (.app (.const numberWeightN) x) rNum :=
  .appElim (B := rNum)
    (.const (type := .pi rNum rNum) (by decide) (fArrow fNum fNum) (LevelTower.IsUniverse.sort _))
        hx

/-- **The count weight map, applied, is an evidence count.** -/
theorem fCountWeight {x : Tm Tower.Head n} (hx : FormationSensitive.Typing weightRules Γ x rNum) :
    FormationSensitive.Typing weightRules Γ (.app (.const countWeightN) x) rEvidenceType :=
  .appElim (B := rEvidenceType)
    (.const (type := .pi rNum rEvidenceType) (by decide) (fArrow fNum fEvidenceType)
      (LevelTower.IsUniverse.sort _)) hx

end Raw

/-! ## The weight carriers and the charge of a row -/

/-- **The two weight carriers of the specimen**: numbers under multiplication, and evidence
counts under the product of packets. -/
inductive Carrier where
  | number
  | count
  deriving DecidableEq, Repr

/-- The type of a carrier's weights. -/
def Carrier.type : Carrier → Tm Tower.Head 0
  | .number => rNum
  | .count => rEvidenceType

/-- The value-to-weight map of a carrier: a declared constant. -/
def Carrier.weight : Carrier → DeclName
  | .number => numberWeightN
  | .count => countWeightN

/-- A literal weight `k` of a carrier: the numeral, or the packet `(evidence k 1)`. -/
def Carrier.literal {n : Nat} : Carrier → Nat → Tm Tower.Head n
  | .number, k => rNumeral k
  | .count, k => rEvidence (rNumeral k) (rNumeral 1)

open Presentation.ScopedComputation in
/-- **Charging a row**: the operation is the stored row; its argument is a weight of the
carrier, and it returns that weight. -/
def gradeSignature (C : Carrier) : OperationSignature Tower.Head Nat where
  input _ := C.type
  output _ := liftClosed C.type

theorem fCarrier (C : Carrier) {n : Nat} {Γ : Ctx Tower.Head n} :
    FormationSensitive.Typing weightRules Γ (liftClosed C.type) (.head (.sort Tower.zero)) := by
  cases C
  · exact fNum
  · exact fEvidenceType

open Presentation.ScopedComputation in
theorem gradeFormation (C : Carrier) (row : Nat) :
    OperationFormation weightRules (gradeSignature C) row := by
  cases C
  · exact ⟨⟨_, LevelTower.IsUniverse.sort _, fNum⟩,
      ⟨_, LevelTower.IsUniverse.sort _, fNum⟩⟩
  · exact ⟨⟨_, LevelTower.IsUniverse.sort _, fEvidenceType⟩,
      ⟨_, LevelTower.IsUniverse.sort _, fEvidenceType⟩⟩

theorem fLiteral (C : Carrier) (k : Nat) {n : Nat} {Γ : Ctx Tower.Head n} :
    FormationSensitive.Typing weightRules Γ (C.literal k) (liftClosed C.type) := by
  cases C
  · exact fNumeral k
  · exact fEvidence (fNumeral k) (fNumeral 1)

theorem fWeightOf (C : Carrier) {n : Nat} {Γ : Ctx Tower.Head n} {x : Tm Tower.Head n}
    (hx : FormationSensitive.Typing weightRules Γ x rNum) :
    FormationSensitive.Typing weightRules Γ (.app (.const C.weight) x) (liftClosed C.type) := by
  cases C
  · exact fNumberWeight hx
  · exact fCountWeight hx


/-! ## The typed computation of the specimen -/

section Specimen

open Presentation.ScopedComputation
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

/-- Weakening of a raw typing by one more variable. -/
theorem fWeaken {n : Nat} {Γ : Ctx Tower.Head n} {A t T : Tm Tower.Head n}
    (typed : FormationSensitive.Typing weightRules Γ t T) :
    FormationSensitive.Typing weightRules (.snoc Γ A) (Presentation.rename wk t)
      (Presentation.rename wk T) :=
  typed.renameTyping fun i => Ctx.lookup_snoc_succ _ _ i

/-- **A stored row with a grade**: it charges its grade, then returns its value. -/
def storedRow {n : Nat} (row : Nat) (grade value : Tm Tower.Head n) : Code Tower.Head Nat n :=
  .sequence (.call row grade) (.returnValue (Presentation.rename wk value))

/-- **The graded identity at its row**, on a selected value: it charges the weight of the
value, computed by the carrier's typed map, then returns the value. -/
def gradedIdentity {n : Nat} (C : Carrier) (row : Nat) (x : Tm Tower.Head n) : Code Tower.Head Nat
    n :=
  .sequence (.call row (.app (.const C.weight) x)) (.returnValue (Presentation.rename wk x))

/-- **The coin**: a choice over its three stored rows, `2` with weight `3` (rows `0` and `1`)
and `5` with weight `7` (row `2`). -/
def coinCode (C : Carrier) : Code Tower.Head Nat 0 :=
  .choose (storedRow 0 (C.literal 3) (rNumeral 2))
    (.choose (storedRow 1 (C.literal 3) (rNumeral 2)) (storedRow 2 (C.literal 7) (rNumeral 5)))

/-- `(weigh-by-self (coin))`: the coin, then the graded identity at row `3` on the selected
value. -/
def producerCode (C : Carrier) : Code Tower.Head Nat 0 :=
  .sequence (coinCode C) (gradedIdentity C 3 (.var 0))

/-- **`(paired (weigh-by-self (coin)))`**: the producer runs once, and its one selected value is
used twice in `Pair`. -/
def sharedPairCode (C : Carrier) : Code Tower.Head Nat 0 :=
  .sequence (producerCode C) (.returnValue (rPair (.var 0) (.var 0)))

/-- **`(weigh-by-self (weigh-by-self 7))`**: the identity at row `2` twice; the outer one charges the
weight of the value the inner one returns. -/
def nestedCode (C : Carrier) : Code Tower.Head Nat 0 :=
  .sequence (gradedIdentity C 2 (rNumeral 7)) (gradedIdentity C 2 (.var 0))

/-- `(weigh-by-self (coin))` over the coin rows `0` (value `0`, no grade) and `1` (value `1`,
weight `3`), with the identity at row `2`. -/
def coinThroughIdCode : Code Tower.Head Nat 0 :=
  .sequence (.choose (.returnValue (rNumeral 0)) (storedRow 1 (Carrier.number.literal 3)
      (rNumeral 1)))
    (gradedIdentity .number 2 (.var 0))

/-- Negative example: **a fresh producer at each use of `paired`**, a different program that
can pair two different selections. -/
def freshPairCode (C : Carrier) : Code Tower.Head Nat 0 :=
  .sequence (producerCode C)
    (.sequence ((producerCode C).rename wk) (.returnValue (rPair (.var 1) (.var 0))))

theorem storedRow_typed (C : Carrier) {n : Nat} {Γ : Ctx Tower.Head n} (row k : Nat)
    {value : Tm Tower.Head n} (hv : FormationSensitive.Typing weightRules Γ value rNum) :
    Typing weightRules (gradeSignature C) Γ (storedRow row (C.literal k) value) rNum := by
  cases C
  · exact .sequence (A := rNum) (B := rNum) fNum (LevelTower.IsUniverse.sort _) fNum
      (LevelTower.IsUniverse.sort _) (.call (gradeFormation .number row) (fLiteral .number k))
      (.returnValue (fWeaken hv))
  · exact .sequence (A := rEvidenceType) (B := rNum) fEvidenceType (LevelTower.IsUniverse.sort _)
      fNum (LevelTower.IsUniverse.sort _) (.call (gradeFormation .count row) (fLiteral .count k))
      (.returnValue (fWeaken hv))

theorem gradedIdentity_typed (C : Carrier) {n : Nat} {Γ : Ctx Tower.Head n} (row : Nat)
    {x : Tm Tower.Head n} (hx : FormationSensitive.Typing weightRules Γ x rNum) :
    Typing weightRules (gradeSignature C) Γ (gradedIdentity C row x) rNum := by
  cases C
  · exact .sequence (A := rNum) (B := rNum) fNum (LevelTower.IsUniverse.sort _) fNum
      (LevelTower.IsUniverse.sort _) (.call (gradeFormation .number row) (fWeightOf .number hx))
      (.returnValue (fWeaken hx))
  · exact .sequence (A := rEvidenceType) (B := rNum) fEvidenceType (LevelTower.IsUniverse.sort _)
      fNum (LevelTower.IsUniverse.sort _) (.call (gradeFormation .count row) (fWeightOf .count hx))
      (.returnValue (fWeaken hx))

theorem coin_typed (C : Carrier) : Typing weightRules (gradeSignature C) .nil (coinCode C) rNum :=
  .choose (storedRow_typed C 0 3 (fNumeral 2))
    (.choose (storedRow_typed C 1 3 (fNumeral 2)) (storedRow_typed C 2 7 (fNumeral 5)))

theorem producer_typed (C : Carrier) :
    Typing weightRules (gradeSignature C) .nil (producerCode C) rNum :=
  .sequence (A := rNum) (B := rNum) fNum (LevelTower.IsUniverse.sort _) fNum
    (LevelTower.IsUniverse.sort _) (coin_typed C) (gradedIdentity_typed C 3 (.var 0))

/-- **The typing derivation of the shared pair**: the coin is a choice over the stored rows,
the identity's grade is the typed weight map at the selected value, and `paired` uses the
one selected value, bound once in its scope, twice. -/
theorem sharedPair_typing (C : Carrier) :
    Typing weightRules (gradeSignature C) .nil (sharedPairCode C) rNumberPair :=
  .sequence (A := rNum) (B := rNumberPair) fNum (LevelTower.IsUniverse.sort _) fNumberPair
    (LevelTower.IsUniverse.sort _) (producer_typed C) (.returnValue (fPair (.var 0) (.var 0)))

/-- **The typing derivation of the nested identity.** -/
theorem nested_typing (C : Carrier) : Typing weightRules (gradeSignature C) .nil (nestedCode C)
    rNum :=
  .sequence (A := rNum) (B := rNum) fNum (LevelTower.IsUniverse.sort _) fNum
    (LevelTower.IsUniverse.sort _) (gradedIdentity_typed C 2 (fNumeral 7))
    (gradedIdentity_typed C 2 (.var 0))

theorem coinThroughId_typing :
    Typing weightRules (gradeSignature .number) .nil coinThroughIdCode rNum :=
  .sequence (A := rNum) (B := rNum) fNum (LevelTower.IsUniverse.sort _) fNum
    (LevelTower.IsUniverse.sort _)
    (.choose (.returnValue (fNumeral 0)) (storedRow_typed .number 1 3 (fNumeral 1)))
    (gradedIdentity_typed .number 2 (.var 0))

/-- The fresh-producer program is typed as well: the typing does not see the difference. -/
theorem freshPair_typing (C : Carrier) :
    Typing weightRules (gradeSignature C) .nil (freshPairCode C) rNumberPair :=
  .sequence (A := rNum) (B := rNumberPair) fNum (LevelTower.IsUniverse.sort _) fNumberPair
    (LevelTower.IsUniverse.sort _) (producer_typed C)
    (.sequence (A := rNum) (B := rNumberPair) fNum (LevelTower.IsUniverse.sort _) fNumberPair
      (LevelTower.IsUniverse.sort _) ((producer_typed C).rename fun i => i.elim0)
      (.returnValue (fPair (.var 1) (.var 0))))

/-! ### The charge primitive, its handler, and the worlds of the specimens -/

/-- What a charge records: the row charged and its grade term. -/
abbrev ChargeRecord := Nat × Tm Tower.Head 0

/-- A closed raw term. -/
abbrev ClosedTerm := Tm Tower.Head 0

/-- A closed program over the charge of a row. -/
abbrev ChargeCode := Code Tower.Head Nat 0

/-- A world of a closed program over the charge of a row: its branch, its answer, and the
charges it recorded, in order. -/
abbrev ChargedWorld := WorldResult Unit (Tm Tower.Head 0) ChargeRecord

/-- **The charge primitive**: one world, which returns the grade and records the row with its
grade. -/
def chargeWorlds : Nat → Tm Tower.Head 0 → Unit → BranchTrace →
    List (WorldResult Unit (Tm Tower.Head 0) ChargeRecord)
  | row, grade, state, branch =>
    [{ branch := branch, answer := grade, state := state, intents := [(row, grade)] }]

/-- The contextual handler of a charge. -/
def chargeHandler : Nat → Tm Tower.Head 0 → Program Unit (Tm Tower.Head 0) ChargeRecord
  | row, grade => .intent (row, grade) (.pure grade)

theorem chargeHandler_realizes (row : Nat) (grade : Tm Tower.Head 0) (state : Unit)
    (branch : BranchTrace) :
    runWorldsAt (chargeHandler row grade) state branch = chargeWorlds row grade state branch :=
  rfl

/-- **The charge primitive returns a weight of its carrier**: its result contract, discharged
for every admitted grade. -/
theorem charge_preserves (C : Carrier) :
    PrimitivePreserves weightRules (gradeSignature C) .nil chargeWorlds := by
  intro row grade state branch output _ admitted returned
  simp only [chargeWorlds, List.mem_singleton] at returned
  subst returned
  cases C
  · exact admitted
  · exact admitted

/-- The ordered worlds of a closed program over the charge primitive. -/
def worldsOf (code : ChargeCode) : List ChargedWorld := Code.worlds chargeWorlds ids code () []

/-- The empty environment is a morphism of the empty context. -/
theorem emptyMor : FormationSensitive.CtxMor weightRules (.nil : Ctx Tower.Head 0) .nil ids :=
  fun i => i.elim0

/-- **Result preservation at the shared pair**: every result of the contextual handler is a
`NumberPair`, by the general theorem with the primitive contract discharged. -/
theorem sharedPair_results (C : Carrier) {output : WorldResult Unit (Tm Tower.Head 0) ChargeRecord}
    (returned :
      output ∈ runWorldsAt (Code.interpret chargeHandler ids (sharedPairCode C)) () []) :
    FormationSensitive.Judgment weightRules .nil output.answer rNumberPair :=
  (⟨.nil, sharedPair_typing C⟩ : Judgment weightRules (gradeSignature C) .nil (sharedPairCode C)
    rNumberPair).interpret_preserve chargeHandler chargeWorlds chargeHandler_realizes .nil emptyMor
    (charge_preserves C) returned

/-- **Result preservation at the nested identity.** -/
theorem nested_results (C : Carrier) {output : WorldResult Unit (Tm Tower.Head 0) ChargeRecord}
    (returned : output ∈ runWorldsAt (Code.interpret chargeHandler ids (nestedCode C)) () []) :
    FormationSensitive.Judgment weightRules .nil output.answer rNum :=
  (⟨.nil, nested_typing C⟩ : Judgment weightRules (gradeSignature C) .nil (nestedCode C)
    rNum).interpret_preserve chargeHandler chargeWorlds chargeHandler_realizes .nil emptyMor
    (charge_preserves C) returned

/-- The direct worlds of the shared pair have typed results, without the handler. -/
theorem sharedPair_world_results (C : Carrier) {output : WorldResult Unit (Tm Tower.Head 0)
    ChargeRecord}
    (returned : output ∈ worldsOf (sharedPairCode C)) :
    FormationSensitive.Typing weightRules .nil output.answer rNumberPair :=
  (sharedPair_typing C).worlds_preserve emptyMor (charge_preserves C) returned

end Specimen


/-! ## Reading grade terms, and what the reading means in the package -/

section Reading

/-- **The number a grade term denotes**, read through the declared equations: the numerals,
and the weight of a number read as a number. -/
def readNumber {n : Nat} : Tm Tower.Head n → Option Nat
  | .const c => if c = zeroN then some 0 else none
  | .app (.const c) t =>
    if c = sucN then (readNumber t).map (· + 1)
    else if c = numberWeightN then readNumber t else none
  | _ => none

/-- **The evidence counts a grade term denotes**: a packet of two numerals, or the count
weight of a number. -/
def readCount {n : Nat} : Tm Tower.Head n → Option (Nat × Nat)
  | .app (.app (.const c) p) q =>
    if c = evidenceN then (readNumber p).bind fun a => (readNumber q).map fun b => (a, b) else none
  | .app (.const c) t => if c = countWeightN then (readNumber t).map fun a => (a, 1) else none
  | _ => none

theorem readNumber_app_const {n : Nat} (c : DeclName) (t : Tm Tower.Head n) :
    readNumber (.app (.const c) t) =
      if c = sucN then (readNumber t).map (· + 1)
      else if c = numberWeightN then readNumber t else none := rfl

/-- **The reading of a number is its value in the package**: a term read as `k` is typed as a
number and equal in the judgment to the numeral `k`. -/
theorem readNumber_sound : (t : Tm Tower.Head 0) → (k : Nat) → readNumber t = some k →
    CTyped weights .nil (liftTm t) cnum ∧ CEqual weights .nil (liftTm t) (cnumeral k) cnum
  | .var i, _, _ => i.elim0
  | .const c, k, read => by
    unfold readNumber at read
    split at read
    · rename_i same
      subst same
      cases read
      exact ⟨tZero subW, .refl (tZero subW)⟩
    · cases read
  | .app f t, k, read => by
    cases f with
    | const c =>
      rw [readNumber_app_const] at read
      by_cases isSuc : c = sucN
      · subst isSuc
        rw [if_pos rfl] at read
        obtain ⟨k', inner, rfl⟩ := Option.map_eq_some_iff.mp read
        obtain ⟨typed, equal⟩ := readNumber_sound t k' inner
        exact ⟨tSuc subW typed, eSuc subW equal⟩
      · rw [if_neg isSuc] at read
        by_cases isWeight : c = numberWeightN
        · subst isWeight
          rw [if_pos rfl] at read
          obtain ⟨typed, equal⟩ := readNumber_sound t k read
          exact ⟨.appElim (B := cnum) numberWeight_typed typed,
            .trans (numberWeight_rule typed) equal⟩
        · rw [if_neg isWeight] at read
          cases read
    | _ => simp [readNumber] at read
  | .head _, _, read => by simp [readNumber] at read
  | .pi _ _, _, read => by simp [readNumber] at read
  | .sigma _ _, _, read => by simp [readNumber] at read
  | .id _ _ _, _, read => by simp [readNumber] at read
  | .lam _, _, read => by simp [readNumber] at read
  | .pair _ _, _, read => by simp [readNumber] at read
  | .fst _, _, read => by simp [readNumber] at read
  | .snd _, _, read => by simp [readNumber] at read
  | .refl _, _, read => by simp [readNumber] at read

/-- **The reading of evidence counts is their value in the package**: a term read as the
counts `(a, b)` is a packet and equal in the judgment to `evidence a b`. -/
theorem readCount_sound : (t : Tm Tower.Head 0) → (a b : Nat) → readCount t = some (a, b) →
    CTyped weights .nil (liftTm t) cEvidence ∧
      CEqual weights .nil (liftTm t) (cevidence (cnumeral a) (cnumeral b)) cEvidence
  | .var i, _, _, _ => i.elim0
  | .app f q, a, b, read => by
    cases f with
    | app g p =>
      cases g with
      | const c =>
        have unfolded : readCount (.app (.app (.const c) p) q) =
            if c = evidenceN then
              (readNumber p).bind fun x => (readNumber q).map fun y => (x, y)
            else none := rfl
        rw [unfolded] at read
        by_cases isPacket : c = evidenceN
        · subst isPacket
          rw [if_pos rfl] at read
          obtain ⟨x, hx, rest⟩ := Option.bind_eq_some_iff.mp read
          obtain ⟨y, hy, same⟩ := Option.map_eq_some_iff.mp rest
          cases same
          obtain ⟨tp, ep⟩ := readNumber_sound p a hx
          obtain ⟨tq, eq⟩ := readNumber_sound q b hy
          exact ⟨wEvidence tp tq, eEvidence weightProgram_admissible (by member_tac) ep eq⟩
        · rw [if_neg isPacket] at read
          cases read
      | _ => simp [readCount] at read
    | const c =>
      have unfolded : readCount (.app (.const c) q) =
          if c = countWeightN then (readNumber q).map fun x => (x, 1) else none := rfl
      rw [unfolded] at read
      by_cases isWeight : c = countWeightN
      · subst isWeight
        rw [if_pos rfl] at read
        obtain ⟨x, hx, same⟩ := Option.map_eq_some_iff.mp read
        cases same
        obtain ⟨tq, eq⟩ := readNumber_sound q a hx
        exact ⟨.appElim (B := cEvidence) countWeight_typed tq,
          .trans (countWeight_rule tq)
            (eEvidence weightProgram_admissible (by member_tac) eq (.refl (wNumeral 1)))⟩
      · rw [if_neg isWeight] at read
        cases read
    | _ => simp [readCount] at read
  | .const _, _, _, read => by simp [readCount] at read
  | .head _, _, _, read => by simp [readCount] at read
  | .pi _ _, _, _, read => by simp [readCount] at read
  | .sigma _ _, _, _, read => by simp [readCount] at read
  | .id _ _ _, _, _, read => by simp [readCount] at read
  | .lam _, _, _, read => by simp [readCount] at read
  | .pair _ _, _, _, read => by simp [readCount] at read
  | .fst _, _, _, read => by simp [readCount] at read
  | .snd _, _, _, read => by simp [readCount] at read
  | .refl _, _, _, read => by simp [readCount] at read

end Reading

/-! ## A zero-rejecting guard -/

section Guard

open Presentation.ScopedComputation
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

/-- **The charge under a zero-rejecting guard**: a grade whose value is zero produces no
world; every other grade is charged. -/
def guardedWorlds : Nat → Tm Tower.Head 0 → Unit → BranchTrace →
    List (WorldResult Unit (Tm Tower.Head 0) ChargeRecord) :=
  fun row grade state branch =>
    if readNumber grade = some 0 then [] else chargeWorlds row grade state branch

/-- The guarded charge keeps the result contract: what it returns, the charge returns. -/
theorem guarded_preserves :
    PrimitivePreserves weightRules (gradeSignature .number) .nil guardedWorlds := by
  intro row grade state branch output formed admitted returned
  unfold guardedWorlds at returned
  split at returned
  · simp at returned
  · exact charge_preserves .number row grade state branch output formed admitted returned

/-- At the grade `number-weight 0` the guarded charge produces no world. -/
theorem guardedWorlds_zero (row : Nat) (state : Unit) (branch : BranchTrace) :
    guardedWorlds row (.app (.const numberWeightN) (rNumeral 0)) state branch = [] := by
  unfold guardedWorlds
  rw [if_pos (by decide)]

/-- **No contextual handler realizes the guard**: the contextual programs have no abort and
always produce a world. -/
theorem guarded_no_handler :
    ¬ ∃ handler : Nat → Tm Tower.Head 0 → Program Unit (Tm Tower.Head 0) ChargeRecord,
      ∀ row grade state branch,
        runWorldsAt (handler row grade) state branch = guardedWorlds row grade state branch := by
  rintro ⟨handler, realizes⟩
  apply runWorldsAt_ne_nil (handler 2 (.app (.const numberWeightN) (rNumeral 0))) () []
  rw [realizes, guardedWorlds_zero]

/-- The ordered worlds of a closed program under the guarded charge. -/
def guardedWorldsOf (code : ChargeCode) : List ChargedWorld := Code.worlds guardedWorlds ids code ()
    []

/-- **Result preservation under the guard**, for the direct worlds: every result is a number. -/
theorem coinThroughId_guarded_results {output : ChargedWorld}
    (returned : output ∈ guardedWorldsOf coinThroughIdCode) :
    FormationSensitive.Typing weightRules .nil output.answer rNum :=
  coinThroughId_typing.worlds_preserve emptyMor guarded_preserves returned

end Guard


#print axioms weightProgram_admissible
#print axioms weights_model
#print axioms weights_consistent
#print axioms mul_assoc_identity
#print axioms mul_one_left_identity
#print axioms mul_one_right_identity
#print axioms tensor_assoc_identity
#print axioms tensor_one_left_identity
#print axioms tensor_one_right_identity
#print axioms mul_assoc_value
#print axioms tensor_assoc_value
#print axioms numberWeight_typed
#print axioms countWeight_typed
#print axioms numberWeight_not_boolean
#print axioms sharedPair_typing
#print axioms nested_typing
#print axioms coinThroughId_typing
#print axioms freshPair_typing
#print axioms charge_preserves
#print axioms sharedPair_results
#print axioms nested_results
#print axioms readNumber_sound
#print axioms readCount_sound
#print axioms coefficient_six
#print axioms packet_six
#print axioms guarded_preserves
#print axioms guarded_no_handler
#print axioms coinThroughId_guarded_results

end Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.GradedIdentity.Typed
