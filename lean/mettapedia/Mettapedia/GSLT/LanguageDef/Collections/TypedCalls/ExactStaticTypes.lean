import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.InferredTypeSets

/-!
# Exact static types and lower bounds

A static type read from a formal, a field, a callee's range or an inferred set
is a lower bound (`InferredTypeSets.LowerAt`): the value's typing is at least as
general. Lower bounds are enough to discharge a check, read jointly over the
children with each member's variables its own (`InferredTypeSets.build_typed`,
`InferredTypeSets.prepared_iff`); a check of each child alone is not
(`Controls.separately_not_jointly`).

A run may record a static type as its answer's typing only when the type is the
value's **exact** typing (`ExactAt`: the one valid typing, no other entry):

* a literal's class, a symbol's one row (`literal_exactAt`, `symbol_exactAt`);
* a value of a class at a value-class formal (`literal_exactAt` again: the
  prepared check admits only a value of the class);
* a checked build whose parameters HE checks, over exact children, whose
  joint assignments are nonempty: exactly the range under them
  (`semCheck_exactAt`, `build_exactAt`).

Then HE's `get-type` answers, read by their solutions, are the recorded type
alone (`recorded_answers`). A lower bound is not exact: with
`(: Pair (-> $a $b (P $a $b)))`, `(Pair Nil Nil)` under the formals
`(List Number)` has the lower bound `(P (List Number) (List Number))`, while HE
types it `(P (List $a) (List $b))` (`Controls.pair_lower_not_exact`), so
`get-type` would answer differently if the bound were recorded.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ExactStaticTypes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open ShapeTyping StaticEvidence InferredTypeSets

/-- **An exact typing**: the value's one valid typing, and no other entry. -/
abbrev ExactAt (S : Set (Ty Empty)) (st : Stamp) : Prop := st.typs = [Sem.ok S]

theorem lower_of_exact {S : Set (Ty Empty)} {st : Stamp} (h : ExactAt S st) (hS : S.Nonempty) :
    LowerAt S st :=
  ⟨hS, .inr ⟨S, by rw [h]; simp, le_refl _⟩⟩

/-- A value of a class is typed exactly at its class. -/
theorem literal_exactAt (Γ : Decls) (g : GroundedValue) (c : String) (hc : valueClass g = some c) :
    ExactAt {.sym c} (stamp Γ (.grounded g)) := by
  rw [ExactAt, literal_exact Γ g c hc]

/-- A symbol with one row HE reads is typed exactly at its instances. -/
theorem symbol_exactAt (Γ : Decls) (s : String) (τ : Ty String) (h : readRows (Γ s) = [τ]) :
    ExactAt (inst τ) (stamp Γ (.symbol s)) := by
  rw [ExactAt, stamp_symbol, h]
  simp

/-- **HE's check over exact arguments at checked parameters** is the range
under the joint assignments, when they are nonempty. -/
theorem semCheck_exactAt (ρ R : Ty String) :
    ∀ (Ts : List (Ty String)) (Ss : List (Set (Ty Empty))) (ss : List Stamp)
      (Θ : Set (String → Ty Empty)), List.Forall₂ ExactAt Ss ss →
      List.Forall₂ (fun T st => heUnchecked T st.kind = false) Ts ss →
      {θ | θ ∈ Θ ∧ θ ∈ joint Ts Ss}.Nonempty →
      semCheck ρ R Ts ss Θ = [Sem.ok {T | ∃ θ, (θ ∈ Θ ∧ θ ∈ joint Ts Ss) ∧ R.bind θ = T}]
  | [], [], [], Θ, .nil, .nil, _ => by
      simp only [semCheck, List.cons.injEq, Sem.ok.injEq, and_true]
      ext T
      simp [joint]
  | P :: Ps, S :: Ss, st :: ss, Θ, .cons hst rest, .cons hP restP, ne => by
      classical
      obtain ⟨θ0, hθ0, hj0⟩ := ne
      have hjc : ∀ θ, θ ∈ joint (P :: Ps) (S :: Ss) ↔ P.bind θ ∈ S ∧ θ ∈ joint Ps Ss := by
        intro θ
        simp only [joint, Set.mem_ofPred_eq, List.forall₂_cons]
      have hP0 := ((hjc θ0).mp hj0).1
      have hstep : (narrow Θ P S).Nonempty := ⟨θ0, hθ0, hP0⟩
      have hst' : st = ⟨st.kind, [Sem.ok S]⟩ := by
        rw [← hst]
      rw [hst', ShapeTyping.Controls.semCheck_one ρ R P Ps st.kind S ss Θ hP,
        if_pos hstep]
      rw [semCheck_exactAt ρ R Ps Ss ss (narrow Θ P S) rest restP
        ⟨θ0, ⟨hθ0, hP0⟩, ((hjc θ0).mp hj0).2⟩]
      congr 2
      ext T
      constructor
      · rintro ⟨θ, ⟨⟨hθ, hPθ⟩, hj⟩, hT⟩
        exact ⟨θ, ⟨hθ, (hjc θ).mpr ⟨hPθ, hj⟩⟩, hT⟩
      · rintro ⟨θ, ⟨hθ, hj⟩, hT⟩
        exact ⟨θ, ⟨⟨hθ, ((hjc θ).mp hj).1⟩, ((hjc θ).mp hj).2⟩, hT⟩

/-- **A checked build over exact children is typed exactly at the
combination's range**, when HE checks every parameter and the joint assignments
are nonempty: the typing a run may record for the value it built. -/
theorem build_exactAt {Γ : Decls} {c : String} {ρ : Ty String} {Ts : List (Ty String)} {R : Ty String}
    (row : ctorRow Γ c = some (ρ, Ts, R)) (args : List Atom) (Ss : List (Set (Ty Empty)))
    (exact : List.Forall₂ ExactAt Ss (args.map (stamp Γ)))
    (checked : List.Forall₂ (fun T st => heUnchecked T st.kind = false) Ts (args.map (stamp Γ)))
    (ne : (combo Ts R Ss).Nonempty) :
    ExactAt (combo Ts R Ss) (stamp Γ (.expression (.symbol c :: args))) := by
  obtain ⟨rows, split⟩ := ctorRow_spec row
  obtain ⟨T0, θ0, hj0, -⟩ := ne
  have len : Ts.length = args.length := by simpa using checked.length_eq
  rw [ExactAt, stamp_ctor Γ c ρ Ts R rows split, if_pos len]
  simp only
  rw [semCheck_exactAt ρ R Ts Ss _ Set.univ exact checked ⟨θ0, trivial, hj0⟩]
  congr 2
  ext T
  constructor
  · rintro ⟨θ, ⟨-, hj⟩, hT⟩
    exact ⟨θ, hj, hT⟩
  · rintro ⟨θ, hj, hT⟩
    exact ⟨θ, ⟨trivial, hj⟩, hT⟩

/-- **A recorded exact typing is HE's**: `get-type`'s answers, read by their
solutions, are the recorded typing alone. -/
theorem recorded_answers (Γ : Decls) (v : Atom) (S : Set (Ty Empty)) (h : ExactAt S (stamp Γ v)) :
    (answers Γ v).map sols = [S] := by
  rw [answers_sols, stampAnswers, h]
  simp [Sem.okSet]

/-! ## Controls -/

namespace Controls

open ShapeTyping.Controls (tv tc listT gc glist decls decls_nil stamp_nil num)
open InferredTypeSets.Controls (bind_listT joint_cons combo7)

/-- **Each child alone meets its parameter, not jointly**: under `Cons`, a
`Number` meets `$x` and a `(List String)` meets `(List $x)`, and no assignment
does both; HE's check of the pair reads them jointly. -/
theorem separately_not_jointly :
    (∃ θ : String → Ty Empty, (tv "x").bind θ ∈ ({gc "Number"} : Set (Ty Empty))) ∧
      (∃ θ : String → Ty Empty, (listT (tv "x")).bind θ ∈ ({glist (gc "String")} : Set (Ty Empty))) ∧
      combo [tv "x", listT (tv "x")] (listT (tv "x")) [{gc "Number"}, {glist (gc "String")}] = ∅ :=
  ⟨⟨fun _ => gc "Number", rfl⟩, ⟨fun _ => gc "String", by rw [bind_listT]; rfl⟩, combo7⟩

/-- `(: Pair (-> $a $b (P $a $b)))`. -/
def pairRow : Ty String := .app [.sym "->", tv "a", tv "b", .app [.sym "P", tv "a", tv "b"]]

/-- The pair range. -/
def pRange : Ty String := .app [.sym "P", tv "a", tv "b"]

/-- The list rows with `Pair`. -/
def pdecls : Decls := fun s => if s = "Pair" then [pairRow] else decls s

/-- `(P t u)` over ground types. -/
def gpair (t u : Ty Empty) : Ty Empty := .app [.sym "P", t, u]

theorem ctorRow_pair : ctorRow pdecls "Pair" = some (pairRow, [tv "a", tv "b"], pRange) := by
  simp [ctorRow, pdecls, pairRow, pRange, arrowSplit]

theorem stamp_nil_p : stamp pdecls (.symbol "Nil") = ⟨"Symbol", [.ok (inst (listT (tv "x")))]⟩ := by
  rw [stamp_congr (Γ' := decls) (.symbol "Nil")]
  · exact stamp_nil
  · intro s hs
    simp [TypedCertificates.Judgment.leaves] at hs
    subst hs
    simp [pdecls]

theorem bind_pRange (θ : String → Ty Empty) : pRange.bind θ = gpair (θ "a") (θ "b") := by
  simp [pRange, gpair, tv, Ty.bind_app]

theorem joint_pair (θ : String → Ty Empty) (A B : Set (Ty Empty)) :
    θ ∈ joint [tv "a", tv "b"] [A, B] ↔ θ "a" ∈ A ∧ θ "b" ∈ B := by
  simp only [joint, Set.mem_ofPred_eq, List.forall₂_cons, List.forall₂_nil_left_iff, and_true]
  rfl

/-- `(Pair Nil Nil)`. -/
def pairNil : Atom := .expression [.symbol "Pair", .symbol "Nil", .symbol "Nil"]

/-- **HE's typing of `(Pair Nil Nil)`** is exactly `(P (List $a) (List $b))`: two
list types, each its own. -/
theorem pair_exact :
    ExactAt (combo [tv "a", tv "b"] pRange [inst (listT (tv "x")), inst (listT (tv "x"))])
      (stamp pdecls pairNil) := by
  have hnil : ExactAt (inst (listT (tv "x"))) (stamp pdecls (.symbol "Nil")) := by
    rw [ExactAt, stamp_nil_p]
  refine build_exactAt ctorRow_pair [.symbol "Nil", .symbol "Nil"] _ (.cons hnil (.cons hnil .nil))
    (.cons rfl (.cons rfl .nil)) ?_
  refine ⟨_, fun _ => glist (gc "Number"), (joint_pair _ _ _).mpr ⟨?_, ?_⟩, rfl⟩ <;>
    exact ⟨fun _ => gc "Number", by rw [bind_listT]⟩

/-- **A lower bound is not the typing** (`Pair` under the formals
`(List Number)`): the bound `(P (List Number) (List Number))` is below HE's
typing of `(Pair Nil Nil)`, which also allows `(P (List String) (List Number))`;
recording the bound would make `get-type` answer a typing HE does not give. -/
theorem pair_lower_not_exact :
    combo [tv "a", tv "b"] pRange [{glist (gc "Number")}, {glist (gc "Number")}] =
        {gpair (glist (gc "Number")) (glist (gc "Number"))} ∧
      LowerAt {gpair (glist (gc "Number")) (glist (gc "Number"))} (stamp pdecls pairNil) ∧
      ¬ ExactAt {gpair (glist (gc "Number")) (glist (gc "Number"))} (stamp pdecls pairNil) ∧
      (answers pdecls pairNil).map sols ≠ [{gpair (glist (gc "Number")) (glist (gc "Number"))}] := by
  have hset : combo [tv "a", tv "b"] pRange [{glist (gc "Number")}, {glist (gc "Number")}] =
      {gpair (glist (gc "Number")) (glist (gc "Number"))} := by
    ext T
    simp only [combo, Set.mem_ofPred_eq, joint_pair, Set.mem_singleton_iff, bind_pRange]
    constructor
    · rintro ⟨θ, ⟨ha, hb⟩, rfl⟩
      rw [ha, hb]
    · rintro rfl
      exact ⟨fun _ => glist (gc "Number"), ⟨rfl, rfl⟩, rfl⟩
  have hmem : ∀ t u : Ty Empty,
      gpair (glist t) (glist u) ∈ combo [tv "a", tv "b"] pRange [inst (listT (tv "x")), inst (listT (tv "x"))] := by
    intro t u
    refine ⟨fun y => if y = "a" then glist t else glist u, (joint_pair _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
    · exact ⟨fun _ => t, by rw [bind_listT]; simp⟩
    · exact ⟨fun _ => u, by rw [bind_listT]; simp⟩
    · rw [bind_pRange]
      simp
  have hne : (combo [tv "a", tv "b"] pRange [inst (listT (tv "x")), inst (listT (tv "x"))]) ≠
      {gpair (glist (gc "Number")) (glist (gc "Number"))} := by
    intro h
    have := hmem (gc "String") (gc "Number")
    rw [h, Set.mem_singleton_iff] at this
    simp [gpair, glist, gc] at this
  refine ⟨hset, ?_, ?_, ?_⟩
  · refine ⟨⟨_, rfl⟩, .inr ⟨combo [tv "a", tv "b"] pRange [inst (listT (tv "x")), inst (listT (tv "x"))],
      by rw [pair_exact]; simp, ?_⟩⟩
    rintro T rfl
    exact hmem _ _
  · intro h
    have h2 := pair_exact
    rw [ExactAt] at h h2
    rw [h] at h2
    simp only [List.cons.injEq, Sem.ok.injEq, and_true] at h2
    exact hne h2.symm
  · rw [recorded_answers pdecls pairNil _ pair_exact]
    intro h
    simp only [List.cons.injEq, and_true] at h
    exact hne h

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ExactStaticTypes
