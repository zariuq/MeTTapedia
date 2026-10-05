import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.SetsModel

/-!
# A query is a type; its answers are its terms

A query asks a collection of stored occurrences for those whose key is a given one, and
returns a value from each. Run, it gives several answers: one for each stored occurrence that
matches, so an answer that is stored twice comes back twice. This file gives the query its
two other faces in the tower inside the sets, where a type is a set.

**The type** (`cQuery O K key k`): for a set `O` of occurrences, a set `K` of keys, a function
`key : O → K` and a key `k`, the pairs of an occurrence `o : O` with a proof that `key o` is
`k`, `Σ (o : O). Id K (key o) k`.

* It is a set (`query_isSet`), in every package that contains the rules of the tower.
* **An occurrence whose key is `k` gives an answer** (`answer_typed`): the pair of the
  occurrence with the reflexivity of its key. The premise is an equality of the judgment, so
  a key that computes to `k` by the package's steps qualifies.
* An answer gives back its occurrence, the proof that its key is `k`, and the value returned
  (`occurrence_typed`, `evidence_typed`, `return_typed`).

**The set** (`ev_query`, `mem_query`): the value of the type is the set of the pairs `(x, ∅)`
for the occurrences `x` whose key is the value of `k`. So

* **the answers are in one-to-one correspondence with the matching occurrences**
  (`answersEquiv`): the type has exactly one element for each stored occurrence with the key,
  and two occurrences that return one value are two answers. The number of answers with a
  given value is the number of matching occurrences with that value
  (`answersWithValueEquiv`). This is the bag of answers; the set of the values returned is its
  support (`returned_values`);
* the proof that a key is `k` adds nothing: it is the empty set for every answer.

**What the judgment types is an answer in the sets** (`answer_sound`): in a package with a set
model, the occurrence of a closed term of the type is an occurrence with the key. Negative
example: **a key that no occurrence has gives a type with no closed term** (`no_answer`).

**A query followed by a family** (`cQueryThen O K key k F`): the pairs of an answer `q` of a
query with an answer of `F` at `q`. It is a set (`queryThen_isSet`), an answer of the query
and an answer of the family at it give an answer (`answerThen_typed`), and in the sets its
answers are in one-to-one correspondence with the pairs of a matching occurrence and a member
of the family at it (`mem_queryThen`, `answersThenEquiv`): counts add up over the matching
occurrences. Two instances:

* **two queries in a row** (`cSecond`): a second query asked at the value each answer of the
  first returns (`second_isSet`, `second_typed`, `answersSecondEquiv`). The value of the first
  answer is fixed before the second query is asked: an expression with several answers, used
  as an argument, is used one answer at a time;
* **a call to a definition by stored rules** (`cCall`): the rules are stored occurrences with
  a left side and the set of the answers of their right side; the answers of a call are a
  rule whose left side is the call with an answer of its right side (`call_isSet`). In the
  sets they are the answers of the right sides of the matching rules side by side, one copy
  for each rule (`answersCallEquiv`): two rules with one left side and equal right sides give
  every answer twice.

**A directed rule is a map of answers** (`cRule`). An expression with several answers is a
set `I` of answers with the value `v : I → T` each returns. For two of them, `(I, v)` and
`(J, w)`, the type of the rules from the first to the second is the type of the functions
that send each answer of `J` to an answer of `I` with the same value,
`Π (j : J). Σ (i : I). Id T (v i) (w j)`. A rule `l ⟶ r` of a program is a term of it, with
`I` the answers of `l` and `J` the answers of `r`: it says that what `r` returns, `l`
returns, and says nothing in the other direction.

* It is a set (`rule_isSet`); applied to an answer it gives an answer with the same value
  (`rule_apply_typed`); every collection of answers has the rule to itself
  (`rule_refl_typed`).
* In the sets a rule sends every answer of `J` to an answer of `I` with the same value
  (`rule_sound`). Negative example: a value that `J` returns and `I` does not leaves the
  type with no closed term (`no_rule`).

Two rules with one left side, `a ⟶ b` and `a ⟶ c`, are two terms of two rule types. Neither
is an equation, and nothing here makes `b` and `c` equal; reading both rules as equations is
a coarser theory, which does.

A rule type speaks of values, not of counts: two answers of `J` may be sent to one answer of
`I`. Counts are kept by the definition as a whole (`answersCallEquiv`).

Not here: the stored occurrences as atoms of a space and the key as a pattern with variables
(that needs the data terms as one set and their constructors read by name), and rules whose
left sides have variables, matched by unification. No statement here says that running
stops.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace MegalodonHOTG
namespace Queries

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.SetTheory.ZFSetOrderedPair (first first_pair second second_pair)
open ZFSetDependentProducts (sigmaSet mem_sigmaSet)
open ZFSetTraceProducts (traceApp tracePiSet traceApp_mem)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)

universe u

variable {L : Type} [LevelOrder L]

/-! ## The terms -/

section Terms

variable {n : Nat}

/-- **The type of the answers of a query**: the occurrences `o : O` whose key `key o` is `k`,
each with the proof that it is. -/
abbrev cQuery (O K key k : CTm (Head L) n) : CTm (Head L) n :=
  .sigma O (.id (K.rename wk) (.app (key.rename wk) (.var 0)) (k.rename wk))

/-- The answer an occurrence gives: the occurrence with the reflexivity of its key. -/
abbrev cAnswer (key o : CTm (Head L) n) : CTm (Head L) n := .pair o (.refl (.app key o))

/-- The value an answer returns: `val` at its occurrence. -/
abbrev cReturn (val q : CTm (Head L) n) : CTm (Head L) n := .app val (.fst q)

omit [LevelOrder L] in
/-- The condition of a query at an occurrence. -/
theorem condition_inst (K key k o : CTm (Head L) n) :
    CTm.inst0 o (.id (K.rename wk) (.app (key.rename wk) (.var 0)) (k.rename wk)) =
      .id K (.app key o) k := by
  show CTm.id (CTm.inst0 o (K.rename wk)) (.app (CTm.inst0 o (key.rename wk)) o)
    (CTm.inst0 o (k.rename wk)) = _
  rw [CTm.inst0_rename_wk, CTm.inst0_rename_wk, CTm.inst0_rename_wk]

omit [LevelOrder L] in
/-- A substitution acts on the type of the answers through its four parts. -/
theorem query_subst {m : Nat} (σ : CSub (Head L) n m) (O K key k : CTm (Head L) n) :
    (cQuery O K key k).subst σ =
      cQuery (O.subst σ) (K.subst σ) (key.subst σ) (k.subst σ) := by
  show CTm.sigma (O.subst σ) (.id ((K.rename wk).subst (CTm.liftSub σ))
    (.app ((key.rename wk).subst (CTm.liftSub σ)) (CTm.liftSub σ 0))
    ((k.rename wk).subst (CTm.liftSub σ))) = _
  rw [CTm.subst_liftSub_wk, CTm.subst_liftSub_wk, CTm.subst_liftSub_wk]
  rfl

omit [LevelOrder L] in
/-- A query whose key alone mentions the newest variable, at an instance of that variable. -/
theorem query_inst (O K key u : CTm (Head L) n) (k : CTm (Head L) (n + 1)) :
    CTm.inst0 u (cQuery (O.rename wk) (K.rename wk) (key.rename wk) k) =
      cQuery O K key (CTm.inst0 u k) := by
  show CTm.subst (CTm.subst0 u) (cQuery (O.rename wk) (K.rename wk) (key.rename wk) k) = _
  rw [query_subst]
  show cQuery (CTm.inst0 u (O.rename wk)) (CTm.inst0 u (K.rename wk))
    (CTm.inst0 u (key.rename wk)) (CTm.inst0 u k) = _
  rw [CTm.inst0_rename_wk, CTm.inst0_rename_wk, CTm.inst0_rename_wk]

/-- **A query followed by a family of answers at each of its answers**: the pairs of an
answer `q` of the query with an answer of `F` at `q`. -/
abbrev cQueryThen (O K key k : CTm (Head L) n) (F : CTm (Head L) (n + 1)) : CTm (Head L) n :=
  .sigma (cQuery O K key k) F

/-- **The second of two queries in a row**, over the answers of the first: the occurrences of
`O'` whose key is the value `val` returns at the answer. -/
abbrev cSecond (val O' K' key' : CTm (Head L) n) : CTm (Head L) (n + 1) :=
  cQuery (O'.rename wk) (K'.rename wk) (key'.rename wk) (cReturn (val.rename wk) (.var 0))

/-- **The answers of the right side of the rule an answer selects**, for a function `Ans` that
gives each stored rule the set of the answers of its right side. -/
abbrev cRightSide (Ans : CTm (Head L) n) : CTm (Head L) (n + 1) :=
  .app (Ans.rename wk) (.fst (.var 0))

/-- **The answers of a call to a definition by stored rules**: a rule whose left side is the
call, with an answer of its right side. `Rl` is the set of the stored rules and `lhs` their
left sides. -/
abbrev cCall (Rl K lhs c Ans : CTm (Head L) n) : CTm (Head L) n :=
  cQueryThen Rl K lhs c (cRightSide Ans)

omit [LevelOrder L] in
/-- The second query at an answer of the first. -/
theorem second_inst (val O' K' key' q : CTm (Head L) n) :
    CTm.inst0 q (cSecond val O' K' key') = cQuery O' K' key' (cReturn val q) := by
  rw [query_inst]
  show cQuery O' K' key' (.app (CTm.inst0 q (val.rename wk)) (.fst q)) = _
  rw [CTm.inst0_rename_wk]

/-- **The type of the rules from one collection of answers to another.** For answers `I`
returning `v` and answers `J` returning `w`, both with values in `T`: the functions that send
each answer of `J` to an answer of `I` with the same value. A directed rule `l ⟶ r` is a
term of this type, with `I` the answers of `l` and `J` the answers of `r`. -/
abbrev cRule (T I v J w : CTm (Head L) n) : CTm (Head L) n :=
  .pi J (cQuery (I.rename wk) (T.rename wk) (v.rename wk) (.app (w.rename wk) (.var 0)))

end Terms

/-! ## In the judgment -/

section Judgment

variable {R' : Rules (Head L)} {Q : ChurchRules R'} {n : Nat} {Γ : CCtx (Head L) n}
  (contains : Contains R')

include contains in
/-- **A type of pairs over a set, of a family of sets, is a set.** -/
theorem pairs_isSet {A : CTm (Head L) n} {B : CTm (Head L) (n + 1)}
    (domain : CTyped Q Γ A allSets) (family : CTyped Q (.snoc Γ A) B allSets) :
    CTyped Q Γ (.sigma A B) allSets :=
  CDerivable.cumul
    (.sigmaForm domain (contains.isUniverse (.sort _)) family (contains.isUniverse (.sort _))
      (contains.join (.sorts _ _)))
    (contains.cumulative
      (u := .sort (.max (.const (.above 0)) (.const (.above 0)))) (v := .sort (.const (.above 0)))
      fun _ => max_le (le_refl _) (le_refl _))

include contains in
/-- **The identity type of a set is a set.** -/
theorem identity_isSet {A a b : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (ha : CTyped Q Γ a A) (hb : CTyped Q Γ b A) : CTyped Q Γ (.id A a b) allSets :=
  .idForm hA (contains.isUniverse (.sort _)) ha hb

omit [LevelOrder L] in
/-- The key of an occurrence is a key. -/
theorem key_typed {O K key o : CTm (Head L) n} (hkey : CTyped Q Γ key (.pi O (K.rename wk)))
    (ho : CTyped Q Γ o O) : CTyped Q Γ (.app key o) K := by
  have step := CDerivable.appElim (B := K.rename wk) hkey ho
  rw [CTm.inst0_rename_wk] at step
  exact step

omit [LevelOrder L] in
/-- The key of the occurrence a query ranges over. -/
theorem key_var_typed {O K key : CTm (Head L) n}
    (hkey : CTyped Q Γ key (.pi O (K.rename wk))) :
    CTyped Q (.snoc Γ O) (.app (key.rename wk) (.var 0)) (K.rename wk) := by
  have step := CDerivable.appElim (B := (K.rename wk).rename (liftRen wk))
    (hkey.weaken (E := O)) (CDerivable.var (P := Q) (Γ := .snoc Γ O) 0)
  rw [CTm.inst0_var_rename_liftRen_wk] at step
  exact step

include contains in
/-- **The type of the answers of a query is a set.** -/
theorem query_isSet {O K key k : CTm (Head L) n} (hO : CTyped Q Γ O allSets)
    (hK : CTyped Q Γ K allSets) (hkey : CTyped Q Γ key (.pi O (K.rename wk)))
    (hk : CTyped Q Γ k K) : CTyped Q Γ (cQuery O K key k) allSets :=
  pairs_isSet contains hO
    (identity_isSet contains (hK.weaken (E := O)) (key_var_typed hkey) (hk.weaken (E := O)))

include contains in
/-- **An occurrence whose key is `k` gives an answer**: the occurrence with the reflexivity of
its key. The key may be equal to `k` by the steps of the package. -/
theorem answer_typed {O K key k o : CTm (Head L) n} (hO : CTyped Q Γ O allSets)
    (hK : CTyped Q Γ K allSets) (hkey : CTyped Q Γ key (.pi O (K.rename wk)))
    (hk : CTyped Q Γ k K) (ho : CTyped Q Γ o O) (same : CEqual Q Γ (.app key o) k K) :
    CTyped Q Γ (cAnswer key o) (cQuery O K key k) := by
  have keyed : CTyped Q Γ (.app key o) K := key_typed hkey ho
  have retyped : CTyped Q Γ (.refl (.app key o)) (.id K (.app key o) k) :=
    .conv (.reflIntro keyed)
      (.idCong (.refl hK) (contains.isUniverse (.sort _)) (.refl keyed) same)
      (contains.isUniverse (.sort _))
  refine .pairIntro (query_isSet contains hO hK hkey hk) (contains.isUniverse (.sort _)) ho ?_
  rw [condition_inst]
  exact retyped

omit [LevelOrder L] in
/-- An answer gives back its occurrence. -/
theorem occurrence_typed {O K key k q : CTm (Head L) n}
    (hq : CTyped Q Γ q (cQuery O K key k)) : CTyped Q Γ (.fst q) O :=
  .fstElim hq

omit [LevelOrder L] in
/-- An answer gives back the proof that the key of its occurrence is `k`. -/
theorem evidence_typed {O K key k q : CTm (Head L) n}
    (hq : CTyped Q Γ q (cQuery O K key k)) :
    CTyped Q Γ (.snd q) (.id K (.app key (.fst q)) k) := by
  have step := CDerivable.sndElim hq
  rw [condition_inst] at step
  exact step

omit [LevelOrder L] in
/-- **An answer returns a value**: `val` at its occurrence. -/
theorem return_typed {O K T key k val q : CTm (Head L) n}
    (hval : CTyped Q Γ val (.pi O (T.rename wk))) (hq : CTyped Q Γ q (cQuery O K key k)) :
    CTyped Q Γ (cReturn val q) T :=
  key_typed hval (occurrence_typed hq)

omit [LevelOrder L] in
/-- A function into a type that does not depend on its argument, under one more variable. -/
theorem function_weaken {O K f E : CTm (Head L) n} (hf : CTyped Q Γ f (.pi O (K.rename wk))) :
    CTyped Q (.snoc Γ E) (f.rename wk) (.pi (O.rename wk) ((K.rename wk).rename wk)) := by
  have weak := hf.weaken (E := E)
  have same : (CTm.pi O (K.rename wk)).rename wk =
      .pi (O.rename wk) ((K.rename wk).rename wk) := by
    show CTm.pi (O.rename wk) ((K.rename wk).rename (liftRen wk)) = _
    rw [CTm.rename_liftRen_wk]
  rw [same] at weak
  exact weak

include contains in
/-- **A query followed by a family of sets at its answers is a set.** -/
theorem queryThen_isSet {O K key k : CTm (Head L) n} {F : CTm (Head L) (n + 1)}
    (hO : CTyped Q Γ O allSets) (hK : CTyped Q Γ K allSets)
    (hkey : CTyped Q Γ key (.pi O (K.rename wk))) (hk : CTyped Q Γ k K)
    (hF : CTyped Q (.snoc Γ (cQuery O K key k)) F allSets) :
    CTyped Q Γ (cQueryThen O K key k F) allSets :=
  pairs_isSet contains (query_isSet contains hO hK hkey hk) hF

include contains in
/-- **An answer of the query and an answer of the family at it give an answer.** -/
theorem answerThen_typed {O K key k q z : CTm (Head L) n} {F : CTm (Head L) (n + 1)}
    (hO : CTyped Q Γ O allSets) (hK : CTyped Q Γ K allSets)
    (hkey : CTyped Q Γ key (.pi O (K.rename wk))) (hk : CTyped Q Γ k K)
    (hF : CTyped Q (.snoc Γ (cQuery O K key k)) F allSets)
    (hq : CTyped Q Γ q (cQuery O K key k)) (hz : CTyped Q Γ z (CTm.inst0 q F)) :
    CTyped Q Γ (.pair q z) (cQueryThen O K key k F) :=
  .pairIntro (queryThen_isSet contains hO hK hkey hk hF) (contains.isUniverse (.sort _)) hq hz

include contains in
/-- **The second query is a family of sets over the answers of the first.** -/
theorem second_isSet {O K key k val O' K' key' : CTm (Head L) n}
    (hval : CTyped Q Γ val (.pi O (K'.rename wk))) (hO' : CTyped Q Γ O' allSets)
    (hK' : CTyped Q Γ K' allSets) (hkey' : CTyped Q Γ key' (.pi O' (K'.rename wk))) :
    CTyped Q (.snoc Γ (cQuery O K key k)) (cSecond val O' K' key') allSets :=
  query_isSet contains (hO'.weaken (E := cQuery O K key k))
    (hK'.weaken (E := cQuery O K key k)) (function_weaken hkey')
    (key_typed (function_weaken hval) (.fstElim (.var 0)))

omit [LevelOrder L] in
/-- **The second of two answers in a row is an answer of the second query at the value the
first returns.** -/
theorem second_typed {O K key k val O' K' key' z : CTm (Head L) n}
    (hz : CTyped Q Γ z (cQueryThen O K key k (cSecond val O' K' key'))) :
    CTyped Q Γ (.snd z) (cQuery O' K' key' (cReturn val (.fst z))) := by
  have step := CDerivable.sndElim hz
  rw [second_inst] at step
  exact step

omit [LevelOrder L] in
/-- **The answers of the right sides are a family of sets over the matching rules.** -/
theorem rightSide_isSet {Rl K lhs c Ans : CTm (Head L) n}
    (hAns : CTyped Q Γ Ans (.pi Rl allSets)) :
    CTyped Q (.snoc Γ (cQuery Rl K lhs c)) (cRightSide Ans) allSets :=
  key_typed (K := allSets) (function_weaken (K := allSets) hAns) (.fstElim (.var 0))

include contains in
/-- **The answers of a call to a definition by stored rules form a set.** -/
theorem call_isSet {Rl K lhs c Ans : CTm (Head L) n} (hRl : CTyped Q Γ Rl allSets)
    (hK : CTyped Q Γ K allSets) (hlhs : CTyped Q Γ lhs (.pi Rl (K.rename wk)))
    (hc : CTyped Q Γ c K) (hAns : CTyped Q Γ Ans (.pi Rl allSets)) :
    CTyped Q Γ (cCall Rl K lhs c Ans) allSets :=
  queryThen_isSet contains hRl hK hlhs hc (rightSide_isSet hAns)

include contains in
/-- **The type of the rules between two collections of answers is a set.** -/
theorem rule_isSet {T I v J w : CTm (Head L) n} (hT : CTyped Q Γ T allSets)
    (hI : CTyped Q Γ I allSets) (hv : CTyped Q Γ v (.pi I (T.rename wk)))
    (hJ : CTyped Q Γ J allSets) (hw : CTyped Q Γ w (.pi J (T.rename wk))) :
    CTyped Q Γ (cRule T I v J w) allSets :=
  family_isSet contains hJ
    (query_isSet contains (hI.weaken (E := J)) (hT.weaken (E := J)) (function_weaken hv)
      (key_var_typed hw))

omit [LevelOrder L] in
/-- **A rule sends an answer to an answer with the same value.** -/
theorem rule_apply_typed {T I v J w m j : CTm (Head L) n}
    (hm : CTyped Q Γ m (cRule T I v J w)) (hj : CTyped Q Γ j J) :
    CTyped Q Γ (.app m j) (cQuery I T v (.app w j)) := by
  have step := CDerivable.appElim hm hj
  rw [query_inst] at step
  have same : CTm.inst0 j (.app (w.rename wk) (.var 0)) = .app w j := by
    show CTm.app (CTm.inst0 j (w.rename wk)) j = _
    rw [CTm.inst0_rename_wk]
  rw [same] at step
  exact step

include contains in
/-- Positive example: **every collection of answers has the rule to itself**, which sends an
answer to itself. -/
theorem rule_refl_typed {T I v : CTm (Head L) n} (hT : CTyped Q Γ T allSets)
    (hI : CTyped Q Γ I allSets) (hv : CTyped Q Γ v (.pi I (T.rename wk))) :
    CTyped Q Γ (.lam I (cAnswer (v.rename wk) (.var 0))) (cRule T I v I v) :=
  .lamIntro hI (contains.isUniverse (.sort _)) (rule_isSet contains hT hI hv hI hv)
    (contains.isUniverse (.sort _))
    (answer_typed contains (hI.weaken (E := I)) (hT.weaken (E := I)) (function_weaken hv)
      (key_var_typed hv) (.var 0) (.refl (key_var_typed hv)))

end Judgment

/-! ## In the sets -/

section Values

variable {heads : Head L → ZFSet.{u}} {consts : DeclName → ZFSet.{u}} {n : Nat}

omit [LevelOrder L] in
/-- **The value of the type of the answers**: the pairs of an occurrence with a member of the
truth value of "its key is the value of `k`". -/
theorem ev_query (O K key k : CTm (Head L) n) (ρ : Env.{u} n) :
    ev heads consts (cQuery O K key k) ρ =
      sigmaSet (ev heads consts O ρ) fun x =>
        truthCode (traceApp (ev heads consts key ρ) x = ev heads consts k ρ) := by
  show sigmaSet (ev heads consts O ρ) (fun x =>
    truthCode (traceApp (ev heads consts (key.rename wk) (extend ρ x)) x =
      ev heads consts (k.rename wk) (extend ρ x))) = _
  simp only [ev_rename_wk]

omit [LevelOrder L] in
/-- **The answers in the sets**: the pairs `(x, ∅)` for the occurrences `x` whose key is the
value of `k`. -/
theorem mem_query {O K key k : CTm (Head L) n} {ρ : Env.{u} n} {z : ZFSet.{u}} :
    z ∈ ev heads consts (cQuery O K key k) ρ ↔
      ∃ x ∈ ev heads consts O ρ,
        traceApp (ev heads consts key ρ) x = ev heads consts k ρ ∧ z = ZFSet.pair x ∅ := by
  rw [ev_query, mem_sigmaSet]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    obtain ⟨rfl, same⟩ := (mem_truthCode _ _).mp hy
    exact ⟨x, hx, same, rfl⟩
  · rintro ⟨x, hx, same, rfl⟩
    exact ⟨x, hx, ∅, (mem_truthCode _ _).mpr ⟨rfl, same⟩, rfl⟩

omit [LevelOrder L] in
/-- The value of the answer of an occurrence: the occurrence paired with the empty set. -/
theorem ev_answer (key o : CTm (Head L) n) (ρ : Env.{u} n) :
    ev heads consts (cAnswer key o) ρ = ZFSet.pair (ev heads consts o ρ) ∅ := rfl

omit [LevelOrder L] in
/-- The value an answer returns, in the sets. -/
theorem ev_return (val q : CTm (Head L) n) (ρ : Env.{u} n) :
    ev heads consts (cReturn val q) ρ =
      traceApp (ev heads consts val ρ) (first (ev heads consts q ρ)) := rfl

/-- The occurrences with the key, in the sets. -/
def Matching (O key k : CTm (Head L) n) (ρ : Env.{u} n) (x : ZFSet.{u}) : Prop :=
  x ∈ ev heads consts O ρ ∧ traceApp (ev heads consts key ρ) x = ev heads consts k ρ

/-- **The answers are in one-to-one correspondence with the matching occurrences.** -/
noncomputable def answersEquiv (O K key k : CTm (Head L) n) (ρ : Env.{u} n) :
    {z : ZFSet.{u} // z ∈ ev heads consts (cQuery O K key k) ρ} ≃
      {x : ZFSet.{u} // Matching (heads := heads) (consts := consts) O key k ρ x} where
  toFun z := ⟨first z.1, by
    obtain ⟨x, hx, same, equal⟩ := mem_query.mp z.2
    rw [equal, first_pair]
    exact ⟨hx, same⟩⟩
  invFun x := ⟨ZFSet.pair x.1 ∅, mem_query.mpr ⟨x.1, x.2.1, x.2.2, rfl⟩⟩
  left_inv z := by
    obtain ⟨x, _, _, equal⟩ := mem_query.mp z.2
    apply Subtype.ext
    show ZFSet.pair (first z.1) ∅ = z.1
    rw [equal, first_pair]
  right_inv x := by
    apply Subtype.ext
    show first (ZFSet.pair x.1 ∅) = x.1
    rw [first_pair]

/-- **The answers that return a given value are in one-to-one correspondence with the matching
occurrences that have that value.** So the number of times a value is returned is the number
of stored occurrences that match and carry it. -/
noncomputable def answersWithValueEquiv (O K key k val : CTm (Head L) n) (ρ : Env.{u} n)
    (y : ZFSet.{u}) :
    {z : ZFSet.{u} // z ∈ ev heads consts (cQuery O K key k) ρ ∧
        traceApp (ev heads consts val ρ) (first z) = y} ≃
      {x : ZFSet.{u} // Matching (heads := heads) (consts := consts) O key k ρ x ∧
        traceApp (ev heads consts val ρ) x = y} where
  toFun z := ⟨first z.1, by
    obtain ⟨x, hx, same, equal⟩ := mem_query.mp z.2.1
    have value := z.2.2
    rw [equal, first_pair] at value ⊢
    exact ⟨⟨hx, same⟩, value⟩⟩
  invFun x := ⟨ZFSet.pair x.1 ∅, mem_query.mpr ⟨x.1, x.2.1.1, x.2.1.2, rfl⟩, by
    rw [first_pair]
    exact x.2.2⟩
  left_inv z := by
    obtain ⟨x, _, _, equal⟩ := mem_query.mp z.2.1
    apply Subtype.ext
    show ZFSet.pair (first z.1) ∅ = z.1
    rw [equal, first_pair]
  right_inv x := by
    apply Subtype.ext
    show first (ZFSet.pair x.1 ∅) = x.1
    rw [first_pair]

omit [LevelOrder L] in
/-- **The values returned are the values of the matching occurrences.** -/
theorem returned_values {O K key k val : CTm (Head L) n} {ρ : Env.{u} n} {y : ZFSet.{u}} :
    (∃ z ∈ ev heads consts (cQuery O K key k) ρ,
        traceApp (ev heads consts val ρ) (first z) = y) ↔
      ∃ x, Matching (heads := heads) (consts := consts) O key k ρ x ∧
        traceApp (ev heads consts val ρ) x = y := by
  constructor
  · rintro ⟨z, hz, value⟩
    obtain ⟨x, hx, same, rfl⟩ := mem_query.mp hz
    rw [first_pair] at value
    exact ⟨x, ⟨hx, same⟩, value⟩
  · rintro ⟨x, ⟨hx, same⟩, value⟩
    exact ⟨ZFSet.pair x ∅, mem_query.mpr ⟨x, hx, same, rfl⟩, by rw [first_pair]; exact value⟩

omit [LevelOrder L] in
/-- The key of the second query, at an answer of the first. -/
theorem ev_return_var (val : CTm (Head L) n) (ρ : Env.{u} n) (x : ZFSet.{u}) :
    ev heads consts (cReturn (val.rename wk) (.var 0)) (extend ρ (ZFSet.pair x ∅)) =
      traceApp (ev heads consts val ρ) x := by
  show traceApp (ev heads consts (val.rename wk) (extend ρ (ZFSet.pair x ∅)))
    (first (ZFSet.pair x ∅)) = _
  rw [ev_rename_wk, first_pair]

omit [LevelOrder L] in
/-- **The answers of a query followed by a family, in the sets**: the pairs of an answer
`(x, ∅)` of the query with a member of the value of the family at it. -/
theorem mem_queryThen {O K key k : CTm (Head L) n} {F : CTm (Head L) (n + 1)}
    {ρ : Env.{u} n} {z : ZFSet.{u}} :
    z ∈ ev heads consts (cQueryThen O K key k F) ρ ↔
      ∃ x y, Matching (heads := heads) (consts := consts) O key k ρ x ∧
        y ∈ ev heads consts F (extend ρ (ZFSet.pair x ∅)) ∧
        z = ZFSet.pair (ZFSet.pair x ∅) y := by
  show z ∈ sigmaSet (ev heads consts (cQuery O K key k) ρ)
    (fun y => ev heads consts F (extend ρ y)) ↔ _
  rw [mem_sigmaSet]
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩
    obtain ⟨x, hx, same, rfl⟩ := mem_query.mp hq
    exact ⟨x, y, ⟨hx, same⟩, hy, rfl⟩
  · rintro ⟨x, y, ⟨hx, same⟩, hy, rfl⟩
    exact ⟨ZFSet.pair x ∅, mem_query.mpr ⟨x, hx, same, rfl⟩, y, hy, rfl⟩

/-- **The answers of a query followed by a family are in one-to-one correspondence with the
pairs of a matching occurrence and a member of the family at its answer.** So their number
is the sum, over the matching occurrences, of the number of members of the family there. -/
noncomputable def answersThenEquiv (O K key k : CTm (Head L) n) (F : CTm (Head L) (n + 1))
    (ρ : Env.{u} n) :
    {z : ZFSet.{u} // z ∈ ev heads consts (cQueryThen O K key k F) ρ} ≃
      {p : ZFSet.{u} × ZFSet.{u} // Matching (heads := heads) (consts := consts) O key k ρ p.1 ∧
        p.2 ∈ ev heads consts F (extend ρ (ZFSet.pair p.1 ∅))} where
  toFun z := ⟨(first (first z.1), second z.1), by
    obtain ⟨x, y, matching, hy, equal⟩ := mem_queryThen.mp z.2
    show Matching O key k ρ (first (first z.1)) ∧
      second z.1 ∈ ev heads consts F (extend ρ (ZFSet.pair (first (first z.1)) ∅))
    rw [equal, first_pair, first_pair, second_pair]
    exact ⟨matching, hy⟩⟩
  invFun p := ⟨ZFSet.pair (ZFSet.pair p.1.1 ∅) p.1.2,
    mem_queryThen.mpr ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩⟩
  left_inv z := by
    obtain ⟨x, y, _, _, equal⟩ := mem_queryThen.mp z.2
    apply Subtype.ext
    show ZFSet.pair (ZFSet.pair (first (first z.1)) ∅) (second z.1) = z.1
    rw [equal, first_pair, first_pair, second_pair]
  right_inv p := by
    apply Subtype.ext
    show (first (first (ZFSet.pair (ZFSet.pair p.1.1 ∅) p.1.2)),
      second (ZFSet.pair (ZFSet.pair p.1.1 ∅) p.1.2)) = p.1
    rw [first_pair, first_pair, second_pair]

omit [LevelOrder L] in
/-- **The second query at an answer of the first, in the sets**: the answers `(x', ∅)` for the
occurrences `x'` of `O'` whose key is the value the first answer returns. -/
theorem mem_second {val O' K' key' : CTm (Head L) n} {ρ : Env.{u} n} {x y : ZFSet.{u}} :
    y ∈ ev heads consts (cSecond val O' K' key') (extend ρ (ZFSet.pair x ∅)) ↔
      ∃ x' ∈ ev heads consts O' ρ,
        traceApp (ev heads consts key' ρ) x' = traceApp (ev heads consts val ρ) x ∧
        y = ZFSet.pair x' ∅ := by
  rw [mem_query]
  constructor
  · rintro ⟨x', hx', same, rfl⟩
    rw [ev_rename_wk] at hx'
    rw [ev_rename_wk, ev_return_var] at same
    exact ⟨x', hx', same, rfl⟩
  · rintro ⟨x', hx', same, rfl⟩
    refine ⟨x', ?_, ?_, rfl⟩
    · rw [ev_rename_wk]
      exact hx'
    · rw [ev_rename_wk, ev_return_var]
      exact same

/-- **The answers of two queries in a row are in one-to-one correspondence with the pairs of
matching occurrences**: an answer of the first, and an answer of the second at the value the
first returns. An answer of the first query whose value the second matches twice counts
twice. -/
noncomputable def answersSecondEquiv (O K key k val O' K' key' : CTm (Head L) n)
    (ρ : Env.{u} n) :
    {z : ZFSet.{u} // z ∈ ev heads consts (cQueryThen O K key k (cSecond val O' K' key')) ρ} ≃
      {p : ZFSet.{u} × ZFSet.{u} // Matching (heads := heads) (consts := consts) O key k ρ p.1 ∧
        ∃ x' ∈ ev heads consts O' ρ,
          traceApp (ev heads consts key' ρ) x' = traceApp (ev heads consts val ρ) p.1 ∧
          p.2 = ZFSet.pair x' ∅} :=
  (answersThenEquiv O K key k (cSecond val O' K' key') ρ).trans
    (Equiv.subtypeEquivRight fun _ => and_congr_right' mem_second)

omit [LevelOrder L] in
/-- **The right side selected by a rule, in the sets**: the members of the value `Ans` gives
the rule. -/
theorem mem_rightSide {Ans : CTm (Head L) n} {ρ : Env.{u} n} {x y : ZFSet.{u}} :
    y ∈ ev heads consts (cRightSide Ans) (extend ρ (ZFSet.pair x ∅)) ↔
      y ∈ traceApp (ev heads consts Ans ρ) x := by
  show y ∈ traceApp (ev heads consts (Ans.rename wk) (extend ρ (ZFSet.pair x ∅)))
    (first (ZFSet.pair x ∅)) ↔ _
  rw [ev_rename_wk, first_pair]

/-- **The answers of a call to a definition by stored rules are the answers of the right sides
of the matching rules, side by side**: one copy for each rule whose left side is the call. Two
rules with equal right sides contribute their answers twice; a right side with no answer
contributes nothing. -/
noncomputable def answersCallEquiv (Rl K lhs c Ans : CTm (Head L) n) (ρ : Env.{u} n) :
    {z : ZFSet.{u} // z ∈ ev heads consts (cCall Rl K lhs c Ans) ρ} ≃
      {p : ZFSet.{u} × ZFSet.{u} // Matching (heads := heads) (consts := consts) Rl lhs c ρ p.1 ∧
        p.2 ∈ traceApp (ev heads consts Ans ρ) p.1} :=
  (answersThenEquiv Rl K lhs c (cRightSide Ans) ρ).trans
    (Equiv.subtypeEquivRight fun _ => and_congr_right' mem_rightSide)

omit [LevelOrder L] in
/-- **A rule in the sets**: it sends every answer of `J` to an answer of `I` with the same
value. So every value `J` returns is a value `I` returns. -/
theorem rule_sound {T I v J w : CTm (Head L) n} {ρ : Env.{u} n} {m : ZFSet.{u}}
    (hm : m ∈ ev heads consts (cRule T I v J w) ρ) {j : ZFSet.{u}}
    (hj : j ∈ ev heads consts J ρ) :
    ∃ i ∈ ev heads consts I ρ,
      traceApp (ev heads consts v ρ) i = traceApp (ev heads consts w ρ) j := by
  have member : m ∈ tracePiSet (ev heads consts J ρ) (fun x =>
      ev heads consts (cQuery (I.rename wk) (T.rename wk) (v.rename wk)
        (.app (w.rename wk) (.var 0))) (extend ρ x)) := hm
  have fibre := traceApp_mem ⟨m, member⟩ ⟨j, hj⟩
  obtain ⟨i, hi, same, _⟩ := mem_query.mp fibre
  rw [ev_rename_wk] at hi
  have right : ev heads consts (.app (w.rename wk) (.var 0) : CTm (Head L) (n + 1))
      (extend ρ j) = traceApp (ev heads consts w ρ) j := by
    show traceApp (ev heads consts (w.rename wk) (extend ρ j)) j = _
    rw [ev_rename_wk]
  rw [ev_rename_wk, right] at same
  exact ⟨i, hi, same⟩

end Values

/-! ## What the judgment types, in the sets -/

section Soundness

variable {R' : Rules (Head L)} {Q : ChurchRules R'} {heads : Head L → ZFSet.{u}}
  {consts : DeclName → ZFSet.{u}} (model : SetModel heads consts Q)

omit [LevelOrder L] in
include model in
/-- **A closed answer is an answer in the sets**: the occurrence of a closed term of the type
of the answers is an occurrence with the key. -/
theorem answer_sound {O K key k q : CTm (Head L) 0}
    (hq : CTyped Q .nil q (cQuery O K key k)) :
    Matching (heads := heads) (consts := consts) O key k Fin.elim0
      (first (ev heads consts q Fin.elim0)) := by
  obtain ⟨x, hx, same, equal⟩ := mem_query.mp (CDerivable.inhabited model hq)
  rw [equal, first_pair]
  exact ⟨hx, same⟩

omit [LevelOrder L] in
include model in
/-- Negative example: **a key that no occurrence has gives a type with no closed term.** -/
theorem no_answer {O K key k : CTm (Head L) 0}
    (none : ∀ x, ¬ Matching (heads := heads) (consts := consts) O key k Fin.elim0 x)
    (q : CTm (Head L) 0) : ¬ CTyped Q .nil q (cQuery O K key k) :=
  fun hq => none _ (answer_sound model hq)

omit [LevelOrder L] in
include model in
/-- Negative example: **a value that the right side returns and the left side does not leaves
the type of the rules with no closed term.** -/
theorem no_rule {T I v J w : CTm (Head L) 0} {j : ZFSet.{u}}
    (hj : j ∈ ev heads consts J Fin.elim0)
    (missing : ∀ i ∈ ev heads consts I Fin.elim0,
      traceApp (ev heads consts v Fin.elim0) i ≠ traceApp (ev heads consts w Fin.elim0) j)
    (m : CTm (Head L) 0) : ¬ CTyped Q .nil m (cRule T I v J w) := fun hm => by
  obtain ⟨i, hi, same⟩ := rule_sound (CDerivable.inhabited model hm) hj
  exact missing i hi same

end Soundness

end Queries
end MegalodonHOTG
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
