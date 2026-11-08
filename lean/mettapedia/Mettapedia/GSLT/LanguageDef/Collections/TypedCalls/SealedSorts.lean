import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypedFoldBound
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RecognizedFolds

/-!
# Sealed sorts: the type relation of PeTTa's `ai` profile, and the cell tests it drops

In PeTTa a function's declaration is read twice: as the contract of its calls
and as the type of an unevaluated application of the function held as data.
The second reading makes every typed producer of a sort a second constructor
of it (`TypedFoldBound.typed_producer_opens`), so no type is a representation.
The `ai` profile drops the second reading and keeps everything else.

**The relation** (`sealedInfo`). PeTTa's relation reads a symbol's rows in two
places: as the symbol's own types (a leaf), and as the rows through which an
application headed by the symbol is typed (`funTrees`). The profile's relation
reads the heads' rows from `TypedFoldBound.termRows`, which keeps no row of a
function, and the leaves' rows from the declarations. So an application of a
function has only its tuple type, while a function's name keeps its arrow type
and typed higher-order calls are unchanged (`Controls.function_value_typed`,
where `termRows` alone loses it). It is one judgment over two signatures
(`twoRelation`), and PeTTa's relation is the same judgment over one
(`info_eq_two`).

**Only held applications change.** With no functions the profile's relation is
PeTTa's (`sealedInfo_of_no_functions`), and on every value in which no
application is headed by a function it gives the same derivations
(`sealed_cands_eq`, `sealed_count_eq`).

**Sealed sorts are representations.** `SealedListClosed` asks that the list
constructors keep their rows and are no functions, that `termRows` is closed
at lists (`CertifiedSpines.ListClosed`), and that a function's non-arrow row,
which its name carries as data, offers no list. Then a ground value typed
once at `(List τ)` is a spine of `Cons` cells ending in `Nil`
(`sealed_spine_of_count`, `sealedLicensed_of_closed`), whatever functions are
typed; the same holds for the Peano sort (`sealed_nat_spine_of_count`).

**The pass without the cell test** (`trustedOperands`, `trustedRunFold`,
`trustedMachine`) reads every expression as a cell, its recursive field and
operand by position, and stops at the first value that is not an expression:
no head, arity or end test, as CeTTa's fold would run on a licensed argument.
On a spine of the fold's own cells it reads exactly what the tested walk reads
(`trustedOperands_build`), so it answers exactly what the recognized fold
answers (`trustedRunFold_eq_runFold`), and the machine's route with it has the
equations' answers, multiplicities included (`trustedMachine_eq_equations`).
So on an argument typed once at a sealed list or Peano sort, dropping the cell
test changes no answer (`sealed_list_drop`, `sealed_nat_drop`).

**The producer's contract** (`sealed_version_results`). CeTTa lets a fold skip its
argument's check when the argument is the answer of a typed producer whose version
proves its range (`petta_range`). In the profile's relation that proof stands:
when the contract analysis (`Accepted`) types data through constructors only
(`ExprSafe`, `PatSafe`: CeTTa plans an application of a function as a call, and
reads patterns of data), the version's answers on arguments meeting the entry
facts meet its range's fact, at every fuel. Its pieces are the relation's
invariants under functional declarations (`sealed_card_eff`, `sealed_cands_sat`),
constructor inversion and construction (`sealed_ctor_inversion`,
`sealed_ctor_construction`, through `count_ctor_node`), and the analysis' rules
(`sealed_patFact_sound`, `sealed_eval_sound`). So a typed producer's ground answers
at a sealed sort are spines (`producer_answers_spines`, `producer_answers_nat_spines`),
and a fold over them drops its cell test with no analysis of the producer
(`modular_list_drop`, `modular_nat_drop`). On the probe's own `build` and `sum` the
whole chain is a theorem (`Controls.build_accepted`, `Controls.build_answers_spines`,
`Controls.sum_build_drop`).

**Controls.** The held `(build 1 Nil)` is typed once at `(List Number)` by
PeTTa's relation and not by the profile's (`Controls.held_build_stable_vs_sealed`);
on it the pass without the cell test answers `1`, where the recognized fold and
the equations answer nothing (`Controls.held_build_trusted_wrong`); a value
whose end is no `Nil` is likewise read wrong (`Controls.improper_end_trusted`).
`(Cons 1 Nil)` is typed once by both (`Controls.cons_typed_both`). A declared
constructor without equations, `(: pair (-> Number (List Number) (List Number)))`,
is part of the sort, which is then not sealed-closed (`Controls.pair_opens`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SealedSorts

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open TypedCalls.Controls (listOf consRow cons_constructor)
open CertifiedSpines
open TypedFoldBound (termRows)
open RecognizedFolds (Spec machineInt runFold machine PrimExact)

/-! ## The relation over two signatures -/

/-- The leaves of a relation that reads the rows of an application's head from
the first signature and the types of a symbol from the second. -/
def twoLeaf (σ : Decls × Decls) : Atom → Info
  | .symbol s => ⟨σ.1 s, (((σ.2 s).map fun τ => (⟨τ.map DVar.own, []⟩ : Deriv)) : Multiset Deriv)⟩
  | v => leafInfo σ.2 v

/-- PeTTa's type relation with heads and leaves read from two signatures. -/
noncomputable def twoRelation : TypedCertificates.Judgment (Decls × Decls) Info where
  leaf := twoLeaf
  node := nodeInfo

section FullCongr

variable {Sig Sig' J : Type} (R : TypedCertificates.Judgment Sig J)
  (R' : TypedCertificates.Judgment Sig' J) (σ : Sig) (σ' : Sig')

mutual
/-- Two judgments with one node rule and the same leaves judge alike. -/
theorem full_eq_of_leaves (node : R.node = R'.node) (leaf : ∀ a, R.leaf σ a = R'.leaf σ' a) :
    ∀ v : Atom, TypedCertificates.Judgment.full R σ v = TypedCertificates.Judgment.full R' σ' v
  | .expression xs => by
      show R.node (TypedCertificates.Judgment.fullAll R σ xs) =
        R'.node (TypedCertificates.Judgment.fullAll R' σ' xs)
      rw [fullAll_eq_of_leaves node leaf xs, node]
  | .symbol _ => leaf _
  | .var _ => leaf _
  | .grounded _ => leaf _

theorem fullAll_eq_of_leaves (node : R.node = R'.node) (leaf : ∀ a, R.leaf σ a = R'.leaf σ' a) :
    ∀ xs : List Atom,
      TypedCertificates.Judgment.fullAll R σ xs = TypedCertificates.Judgment.fullAll R' σ' xs
  | [] => rfl
  | x :: xs => by
      show TypedCertificates.Judgment.full R σ x :: TypedCertificates.Judgment.fullAll R σ xs =
        TypedCertificates.Judgment.full R' σ' x :: TypedCertificates.Judgment.fullAll R' σ' xs
      rw [full_eq_of_leaves node leaf x, fullAll_eq_of_leaves node leaf xs]
end

end FullCongr

/-- **PeTTa's relation is the two-signature relation over one signature.** -/
theorem info_eq_two (Γ : Decls) (v : Atom) :
    info Γ v = TypedCertificates.Judgment.full twoRelation (Γ, Γ) v :=
  full_eq_of_leaves typeRelation twoRelation Γ (Γ, Γ) rfl (fun a => by cases a <;> rfl) v

/-! ## The profile's relation -/

section Sealed

variable (Γ : Decls) (funs : String → Prop) [DecidablePred funs]

/-- **The type relation of the `ai` profile**: heads read `termRows`, which
keeps no row of a function, so an application of a function is typed only by
its tuple type; a symbol keeps the types of all its rows. -/
noncomputable def sealedInfo (v : Atom) : Info :=
  TypedCertificates.Judgment.full twoRelation (termRows Γ funs, Γ) v

theorem sealedInfo_symbol (s : String) :
    sealedInfo Γ funs (.symbol s) =
      ⟨termRows Γ funs s, (((Γ s).map fun τ => (⟨τ.map DVar.own, []⟩ : Deriv)) : Multiset Deriv)⟩ :=
  rfl

theorem sealedInfo_expression (xs : List Atom) :
    sealedInfo Γ funs (.expression xs) = nodeInfo (xs.map (sealedInfo Γ funs)) :=
  TypedCertificates.Judgment.full_expression twoRelation _ xs

theorem sealedInfo_var (x : String) : sealedInfo Γ funs (.var x) = info Γ (.var x) := rfl

theorem sealedInfo_grounded (g : GroundedValue) :
    sealedInfo Γ funs (.grounded g) = info Γ (.grounded g) := rfl

/-- A symbol's own derivations are the same in both relations. -/
theorem sealedInfo_symbol_cands (s : String) :
    (sealedInfo Γ funs (.symbol s)).cands = (info Γ (.symbol s)).cands := rfl

/-- Some effective derivation of a value meets a ground type, in the profile's relation. -/
def STypable (v : Atom) (T : Ty Empty) : Prop := ∃ d ∈ eff (sealedInfo Γ funs v), Meets d T

theorem stypable_iff_count (v : Atom) (T : Ty Empty) :
    STypable Γ funs v T ↔ 0 < count (sealedInfo Γ funs v) T := by
  classical
  unfold count STypable Meets
  rw [Multiset.card_pos_iff_exists_mem]
  simp only [Multiset.mem_filter]

/-- With no functions, `termRows` is the signature. -/
theorem termRows_of_no_functions (h : ∀ s, ¬ funs s) : termRows Γ funs = Γ := by
  funext s
  simp [termRows, h s]

/-- **With no functions the profile's relation is PeTTa's.** -/
theorem sealedInfo_of_no_functions (h : ∀ s, ¬ funs s) (v : Atom) :
    sealedInfo Γ funs v = info Γ v := by
  rw [info_eq_two]
  unfold sealedInfo
  rw [termRows_of_no_functions Γ funs h]

end Sealed

/-! ## Only held applications of functions are typed otherwise -/

section Agreement

/-- A value's head is no function. -/
def HeadFree (funs : String → Prop) : Atom → Prop
  | .symbol f => ¬ funs f
  | _ => True

/-- The first element of an expression is no function. -/
def HeadFreeList (funs : String → Prop) : List Atom → Prop
  | x :: _ => HeadFree funs x
  | [] => True

mutual
/-- **No application of a function** anywhere in a value: every expression's
head is no function. -/
def NoHeldCalls (funs : String → Prop) : Atom → Prop
  | .expression xs => HeadFreeList funs xs ∧ NoHeldCallsAll funs xs
  | .symbol _ => True
  | .var _ => True
  | .grounded _ => True

/-- The list version. -/
def NoHeldCallsAll (funs : String → Prop) : List Atom → Prop
  | [] => True
  | x :: xs => NoHeldCalls funs x ∧ NoHeldCallsAll funs xs
end

theorem eff_eq_of_cands {j j' : Info} (h : j.cands = j'.cands) : eff j = eff j' := by
  unfold eff
  rw [h]

theorem argEqs_eff : ∀ (i : ℕ) (As : List (Ty String)) (js js' : List Info),
    List.Forall₂ (fun j j' => eff j = eff j') js js' → argEqs i As js = argEqs i As js'
  | _, [], [], [], _ => rfl
  | _, [], _ :: _, _ :: _, _ => rfl
  | _, _ :: _, [], [], _ => rfl
  | i, A :: As, j :: js, j' :: js', .cons hj hjs => by
      simp only [argEqs, hj, argEqs_eff (i + 1) As js js' hjs]
  | _, [], [], _ :: _, h => by cases h
  | _, [], _ :: _, [], h => by cases h
  | _, _ :: _, [], _ :: _, h => by cases h
  | _, _ :: _, _ :: _, [], h => by cases h

theorem tupleParts_eff : ∀ (i : ℕ) (js js' : List Info),
    List.Forall₂ (fun j j' => eff j = eff j') js js' → tupleParts i js = tupleParts i js'
  | _, [], [], _ => rfl
  | i, j :: js, j' :: js', .cons hj hjs => by
      simp only [tupleParts, hj, tupleParts_eff (i + 1) js js' hjs]
  | _, [], _ :: _, h => by cases h
  | _, _ :: _, [], h => by cases h

/-- An expression's record reads its head's rows and every element's derivations. -/
theorem nodeInfo_eff {j j' : Info} {js js' : List Info} (rows : j.rows = j'.rows)
    (hj : eff j = eff j') (hjs : List.Forall₂ (fun j j' => eff j = eff j') js js') :
    nodeInfo (j :: js) = nodeInfo (j' :: js') := by
  have funT : funTrees j js = funTrees j' js' := by
    unfold funTrees
    rw [rows, hjs.length_eq]
    congr 1
    funext τ
    split
    · rw [argEqs_eff 1 _ js js' hjs]
    · rfl
  simp only [nodeInfo, funT, tupleTrees, tupleParts_eff 0 _ _ (List.Forall₂.cons hj hjs)]

variable (Γ : Decls) (funs : String → Prop) [DecidablePred funs]

/-- The rows of a value that is not a symbol are none, in both relations. -/
theorem rows_nonsymbol_eq : ∀ v : Atom, (∀ s, v ≠ .symbol s) →
    (sealedInfo Γ funs v).rows = (info Γ v).rows
  | .symbol s, h => (h s rfl).elim
  | .var _, _ => rfl
  | .grounded g, _ => rfl
  | .expression xs, _ => by
      rw [sealedInfo_expression, info_expression]
      cases xs <;> rfl

mutual
/-- **The profile's relation gives every value without a held application of a
function the derivations PeTTa's relation gives it**, and the same rows where
the value is not a function's name. -/
theorem sealed_agree : ∀ v : Atom, NoHeldCalls funs v →
    (sealedInfo Γ funs v).cands = (info Γ v).cands ∧
      (HeadFree funs v → (sealedInfo Γ funs v).rows = (info Γ v).rows)
  | .symbol s, _ => ⟨rfl, fun hf => by
      simp only [sealedInfo_symbol, info_symbol, termRows]
      simp only [HeadFree] at hf
      simp [hf]⟩
  | .var _, _ => ⟨rfl, fun _ => rfl⟩
  | .grounded _, _ => ⟨rfl, fun _ => rfl⟩
  | .expression [], _ => ⟨rfl, fun _ => rfl⟩
  | .expression (x :: xs), ⟨hhead, hx, hxs⟩ => by
      have ih := sealed_agree x hx
      have rowsX : (sealedInfo Γ funs x).rows = (info Γ x).rows := by
        by_cases hs : ∃ s, x = .symbol s
        · obtain ⟨s, rfl⟩ := hs
          exact ih.2 hhead
        · exact rows_nonsymbol_eq Γ funs x fun s hs' => hs ⟨s, hs'⟩
      have same : nodeInfo (sealedInfo Γ funs x :: xs.map (sealedInfo Γ funs)) =
          nodeInfo (info Γ x :: xs.map (info Γ)) :=
        nodeInfo_eff rowsX (eff_eq_of_cands ih.1) (sealed_agreeAll xs hxs)
      rw [sealedInfo_expression, info_expression, List.map_cons, List.map_cons, same]
      exact ⟨rfl, fun _ => rfl⟩

/-- The list version. -/
theorem sealed_agreeAll : ∀ xs : List Atom, NoHeldCallsAll funs xs →
    List.Forall₂ (fun j j' => eff j = eff j') (xs.map (sealedInfo Γ funs)) (xs.map (info Γ))
  | [], _ => .nil
  | x :: xs, ⟨hx, hxs⟩ => .cons (eff_eq_of_cands (sealed_agree x hx).1) (sealed_agreeAll xs hxs)
end

theorem sealed_cands_eq (v : Atom) (h : NoHeldCalls funs v) :
    (sealedInfo Γ funs v).cands = (info Γ v).cands :=
  (sealed_agree Γ funs v h).1

/-- **Off held applications, the profile counts as PeTTa does**, at every type. -/
theorem sealed_count_eq (v : Atom) (h : NoHeldCalls funs v) (T : Ty Empty) :
    count (sealedInfo Γ funs v) T = count (info Γ v) T := by
  unfold count
  rw [eff_eq_of_cands (sealed_cands_eq Γ funs v h)]

end Agreement

/-! ## Reading the profile's relation -/

section Reading

variable {Γ : Decls} {funs : String → Prop} [DecidablePred funs]

theorem sealed_mem_symbol_cands {s : String} {d : Deriv}
    (h : d ∈ (sealedInfo Γ funs (.symbol s)).cands) :
    ∃ ρ ∈ Γ s, d = ⟨ρ.map DVar.own, []⟩ :=
  mem_symbol_cands (by rw [← sealedInfo_symbol_cands Γ funs s]; exact h)

theorem sealed_mem_expression_cands {x : Atom} {xs : List Atom} {d : Deriv}
    (h : d ∈ (sealedInfo Γ funs (.expression (x :: xs))).cands) :
    d ∈ funTrees (sealedInfo Γ funs x) (xs.map (sealedInfo Γ funs)) ∨
      d ∈ tupleTrees (sealedInfo Γ funs x :: xs.map (sealedInfo Γ funs)) := by
  rw [sealedInfo_expression, List.map_cons] at h
  simp only [nodeInfo] at h
  split_ifs at h
  · right
    exact h
  · left
    exact h

/-- Only a symbol has rows, and a symbol's are its `termRows`. -/
theorem sealed_rows : ∀ v : Atom, (sealedInfo Γ funs v).rows = match v with
    | .symbol s => termRows Γ funs s
    | _ => []
  | .symbol _ => rfl
  | .var _ => rfl
  | .grounded g => by cases g <;> rfl
  | .expression xs => by
      rw [sealedInfo_expression]
      cases xs <;> rfl

end Reading

/-! ## Sealed list sorts -/

section SealedList

variable {Γ : Decls} {funs : String → Prop} [DecidablePred funs]

variable (Γ funs) in
/-- **The list sort is sealed-closed**: under `termRows` the list sort is closed
(the constructors keep their rows, and every other row that types an
application offers a type away from lists), and every non-arrow row of a
function, which its name carries as data, offers no list either. -/
structure SealedListClosed : Prop where
  heads : ListClosed (termRows Γ funs)
  leaves : ∀ s, funs s → ∀ ρ ∈ Γ s, arrowSplit ρ = none → AwayFromList ρ

theorem SealedListClosed.nil_not_fun (h : SealedListClosed Γ funs) : ¬ funs "Nil" := by
  intro hf
  have := h.heads.nil
  simp [termRows, hf] at this

theorem SealedListClosed.cons_not_fun (h : SealedListClosed Γ funs) : ¬ funs "Cons" := by
  intro hf
  have := h.heads.cons
  simp [termRows, hf] at this

theorem SealedListClosed.nil (h : SealedListClosed Γ funs) : Γ "Nil" = [listOf (.var "a")] := by
  have := h.heads.nil
  simpa [termRows, h.nil_not_fun] using this

theorem SealedListClosed.cons (h : SealedListClosed Γ funs) : Γ "Cons" = [consRow] := by
  have := h.heads.cons
  simpa [termRows, h.cons_not_fun] using this

/-- No row of a symbol other than `Nil`, read as the symbol's own type, is a list
type or the bare `List`. -/
theorem sealed_leaf_ne (h : SealedListClosed Γ funs) {s : String} {ρ : Ty String}
    (hρ : ρ ∈ Γ s) (notNil : s ≠ "Nil") (f : String → Ty Empty) :
    ρ.bind f ≠ .sym "List" ∧ ∀ τ : Ty Empty, ρ.bind f ≠ listOf τ := by
  by_cases hf : funs s
  · cases hs : arrowSplit ρ with
    | none => exact away_ne (h.leaves s hf ρ hρ hs) f
    | some p =>
        obtain ⟨ts, rfl⟩ := arrowSplit_head hs
        exact arrow_ne f
  · exact row_ne h.heads (by simpa [termRows, hf] using hρ) notNil f

/-- **No ground value meets the bare `List`** in the profile's relation, under a
sealed-closed list sort. -/
theorem sealed_not_meets_bareList (h : SealedListClosed Γ funs) :
    ∀ v : Atom, Ground v → ∀ d ∈ eff (sealedInfo Γ funs v), ¬ Meets d (.sym "List")
  | .var _, hg, _, _, _ => hg
  | .symbol s, _, d, hd, hm => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rcases mem_eff hd with hc | rfl
      · obtain ⟨ρ, hρ, rfl⟩ := sealed_mem_symbol_cands hc
        simp only [Ty.bind_map] at hty
        by_cases isNil : s = "Nil"
        · subst isNil
          rw [h.nil, List.mem_singleton] at hρ
          subst hρ
          exact nil_row_ne _ hty
        · exact (sealed_leaf_ne h hρ isNil _).1 hty
      · simp [undefinedDeriv, undefinedTy] at hty
  | .grounded g, _, d, hd, hm => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rw [sealedInfo_grounded] at hd
      rcases grounded_ty hd with rfl | ⟨c, hc, rfl⟩
      · simp [undefinedDeriv, undefinedTy] at hty
      · rcases hc with rfl | rfl | rfl <;> simp [classDeriv] at hty
  | .expression [], _, d, hd, hm => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rcases mem_eff hd with hc | rfl
      · rw [sealedInfo_expression] at hc
        simp only [List.map_nil, nodeInfo, tupleTrees, tupleParts, Multiset.map_singleton,
          Multiset.mem_singleton] at hc
        subst hc
        simp at hty
      · simp [undefinedDeriv, undefinedTy] at hty
  | .expression (x :: xs), _, d, hd, hm => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rcases mem_eff hd with hc | rfl
      · rcases sealed_mem_expression_cands hc with hf | ht
        · obtain ⟨ρ, hρ, As, R, hs, -, E, -, rfl⟩ := mem_funTrees hf
          simp only [Ty.bind_map] at hty
          rw [sealed_rows] at hρ
          match x, hρ with
          | .symbol s, hρ =>
              simp only at hρ
              by_cases isNil : s = "Nil"
              · subst isNil
                rw [h.heads.nil, List.mem_singleton] at hρ
                subst hρ
                simp [arrowSplit, listOf] at hs
              by_cases isCons : s = "Cons"
              · subst isCons
                rw [h.heads.cons, List.mem_singleton] at hρ
                subst hρ
                simp only [consRow, arrowSplit_arrow, Option.some.injEq, Prod.mk.injEq] at hs
                obtain ⟨-, rfl⟩ := hs
                simp [listOf] at hty
              · have away := h.heads.other s isNil isCons ρ hρ
                simp only [offered, hs] at away
                exact (away_ne away _).1 hty
        · obtain ⟨dh, -, p, -, rfl⟩ := mem_tupleTrees_cons ht
          simp at hty
      · simp [undefinedDeriv, undefinedTy] at hty

/-- **The list sort's inversion in the profile's relation**: a ground value typable
at `(List τ)` is `Nil`, or a `Cons` of a value typable at `τ` and a value typable
at `(List τ)`. -/
theorem sealed_list_inversion (h : SealedListClosed Γ funs) (τ : Ty Empty) :
    ∀ v : Atom, Ground v → STypable Γ funs v (listOf τ) →
      v = .symbol "Nil" ∨
        ∃ x r, v = .expression [.symbol "Cons", x, r] ∧ STypable Γ funs x τ ∧
          STypable Γ funs r (listOf τ)
  | .var _, hg, _ => hg.elim
  | .symbol s, _, ⟨d, hd, hm⟩ => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rcases mem_eff hd with hc | rfl
      · obtain ⟨ρ, hρ, rfl⟩ := sealed_mem_symbol_cands hc
        simp only [Ty.bind_map] at hty
        by_cases isNil : s = "Nil"
        · exact .inl (by rw [isNil])
        · exact absurd hty ((sealed_leaf_ne h hρ isNil _).2 τ)
      · simp [undefinedDeriv, undefinedTy, listOf] at hty
  | .grounded g, _, ⟨d, hd, hm⟩ => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rw [sealedInfo_grounded] at hd
      rcases grounded_ty hd with rfl | ⟨c, -, rfl⟩
      · simp [undefinedDeriv, undefinedTy, listOf] at hty
      · simp [classDeriv, listOf] at hty
  | .expression [], _, ⟨d, hd, hm⟩ => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rcases mem_eff hd with hc | rfl
      · rw [sealedInfo_expression] at hc
        simp only [List.map_nil, nodeInfo, tupleTrees, tupleParts, Multiset.map_singleton,
          Multiset.mem_singleton] at hc
        subst hc
        simp [listOf] at hty
      · simp [undefinedDeriv, undefinedTy, listOf] at hty
  | .expression (x :: xs), hg, ⟨d, hd, hm⟩ => by
      obtain ⟨σ, hs, hty⟩ := meets_iff.mp hm
      have hgx : Ground x := hg.1
      rcases mem_eff hd with hc | rfl
      · rcases sealed_mem_expression_cands hc with hf | ht
        · obtain ⟨ρ, hρ, As, R, hsplit, hlen, E, hE, rfl⟩ := mem_funTrees hf
          simp only [Ty.bind_map] at hty
          rw [sealed_rows] at hρ
          match x, hρ, hgx with
          | .symbol s, hρ, _ =>
              simp only at hρ
              by_cases isNil : s = "Nil"
              · subst isNil
                rw [h.heads.nil, List.mem_singleton] at hρ
                subst hρ
                simp [arrowSplit, listOf] at hsplit
              by_cases isCons : s = "Cons"
              · subst isCons
                rw [h.heads.cons, List.mem_singleton] at hρ
                subst hρ
                simp only [consRow, arrowSplit_arrow, Option.some.injEq, Prod.mk.injEq] at hsplit
                obtain ⟨rfl, rfl⟩ := hsplit
                match xs, hlen with
                | [y, r], _ =>
                    right
                    refine ⟨y, r, rfl, ?_⟩
                    have hu1 : ¬ Unchecked (Ty.var "a" : Ty String) := by simp [Unchecked]
                    have hu2 : ¬ Unchecked (listOf (Ty.var "a") : Ty String) := by
                      simp [Unchecked, listOf]
                    rw [List.map_cons, List.map_cons, List.map_nil, argEqs_cons_checked hu1,
                      Multiset.mem_bind] at hE
                    obtain ⟨dy, hdy, hE⟩ := hE
                    rw [Multiset.mem_map] at hE
                    obtain ⟨E2, hE2, rfl⟩ := hE
                    rw [argEqs_cons_checked hu2, Multiset.mem_bind] at hE2
                    obtain ⟨dr, hdr, hE2⟩ := hE2
                    rw [argEqs, Multiset.map_singleton, Multiset.mem_singleton] at hE2
                    subst hE2
                    simp only [List.append_nil, List.cons_append, solves_cons, solves_append] at hs
                    obtain ⟨ha, hy, hl, hr⟩ := hs
                    have hτ : σ (DVar.own "a") = τ := by
                      simp only [listOf, Ty.bind_app, List.map_cons, List.map_nil, Ty.bind_sym,
                        Ty.app.injEq, List.cons.injEq, and_true, true_and] at hty
                      simpa [Function.comp] using hty
                    refine ⟨⟨dy, hdy, meets_of_pushed hy ?_⟩, ⟨dr, hdr, meets_of_pushed hr ?_⟩⟩
                    · rw [← ha]
                      simpa using hτ
                    · rw [← hl]
                      simp [listOf, hτ]
              · have away := h.heads.other s isNil isCons ρ hρ
                simp only [offered, hsplit] at away
                exact absurd hty ((away_ne away _).2 τ)
        · obtain ⟨dh, hdh, p, -, rfl⟩ := mem_tupleTrees_cons ht
          rw [solves_append] at hs
          simp only [Ty.bind_app, List.map_cons, listOf, Ty.app.injEq, List.cons.injEq] at hty
          exact absurd (meets_of_pushed hs.1 hty.1) (sealed_not_meets_bareList h x hgx dh hdh)
      · simp [undefinedDeriv, undefinedTy, listOf] at hty

/-- **A value typed at a sealed list sort is a spine of the fold's own cells.** -/
theorem sealed_spine_of_typable (h : SealedListClosed Γ funs) (τ : Ty Empty) (v : Atom)
    (hg : Ground v) (ht : STypable Γ funs v (listOf τ)) :
    ConsSpine (fun x => STypable Γ funs x τ) v := by
  induction hn : sizeOf v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
      rcases sealed_list_inversion h τ v hg ht with rfl | ⟨x, r, rfl, hx, hr⟩
      · exact .nil
      · refine .cons x r hx (ih (sizeOf r) ?_ r (ground_cons_parts hg).2 hr rfl)
        subst hn
        simp
        omega

theorem sealed_spine_of_count (h : SealedListClosed Γ funs) (τ : Ty Empty) (v : Atom)
    (hg : Ground v) (one : count (sealedInfo Γ funs v) (listOf τ) = 1) :
    ConsSpine (fun x => STypable Γ funs x τ) v :=
  sealed_spine_of_typable h τ v hg ((stypable_iff_count Γ funs v _).mpr (by omega))

variable (Γ funs) in
/-- **The profile's relation licenses the pass without the cell test at `(List τ)`**:
every ground value it types once there is a spine. -/
def SealedLicensed (τ : Ty Empty) : Prop :=
  ∀ v : Atom, Ground v → count (sealedInfo Γ funs v) (listOf τ) = 1 → ConsSpine (fun _ => True) v

theorem sealedLicensed_of_closed (h : SealedListClosed Γ funs) (τ : Ty Empty) :
    SealedLicensed Γ funs τ := fun v hg one =>
  TypedFoldBound.spine_true (sealed_spine_of_count h τ v hg one)

/-- The hypotheses of `TypedFoldBound.sealed_closed` give a sealed-closed sort as soon
as no function carries a list as a non-arrow row. -/
theorem sealedListClosed_of (hNil : Γ "Nil" = [listOf (.var "a")]) (hCons : Γ "Cons" = [consRow])
    (fNil : ¬ funs "Nil") (fCons : ¬ funs "Cons")
    (others : ∀ s, ¬ funs s → s ≠ "Nil" → s ≠ "Cons" → ∀ ρ ∈ Γ s, AwayFromList (offered ρ))
    (leaves : ∀ s, funs s → ∀ ρ ∈ Γ s, arrowSplit ρ = none → AwayFromList ρ) :
    SealedListClosed Γ funs :=
  ⟨TypedFoldBound.sealed_closed hNil hCons fNil fCons others, leaves⟩

end SealedList

/-! ## Sealed Peano sorts -/

section SealedNat

variable {Γ : Decls} {funs : String → Prop} [DecidablePred funs]

variable (Γ funs) in
/-- **The Peano sort is sealed-closed.** -/
structure SealedNatClosed : Prop where
  heads : NatClosed (termRows Γ funs)
  leaves : ∀ s, funs s → ∀ ρ ∈ Γ s, arrowSplit ρ = none → AwayFromNat ρ

theorem SealedNatClosed.zero_not_fun (h : SealedNatClosed Γ funs) : ¬ funs "Z" := by
  intro hf
  have := h.heads.zero
  simp [termRows, hf] at this

theorem SealedNatClosed.succ_not_fun (h : SealedNatClosed Γ funs) : ¬ funs "S" := by
  intro hf
  have := h.heads.succ
  simp [termRows, hf] at this

theorem SealedNatClosed.succ (h : SealedNatClosed Γ funs) : Γ "S" = [arrow [.sym "Nat"] (.sym "Nat")] := by
  have := h.heads.succ
  simpa [termRows, h.succ_not_fun] using this

/-- **The Peano sort's inversion in the profile's relation.** -/
theorem sealed_nat_inversion (h : SealedNatClosed Γ funs) :
    ∀ v : Atom, Ground v → STypable Γ funs v (.sym "Nat") →
      v = .symbol "Z" ∨ ∃ n, v = .expression [.symbol "S", n] ∧ STypable Γ funs n (.sym "Nat")
  | .var _, hg, _ => hg.elim
  | .symbol s, _, ⟨d, hd, hm⟩ => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rcases mem_eff hd with hc | rfl
      · obtain ⟨ρ, hρ, rfl⟩ := sealed_mem_symbol_cands hc
        simp only [Ty.bind_map] at hty
        by_cases isZ : s = "Z"
        · exact .inl (by rw [isZ])
        by_cases isS : s = "S"
        · subst isS
          rw [h.succ, List.mem_singleton] at hρ
          subst hρ
          simp [arrow] at hty
        · cases hs : arrowSplit ρ with
          | none =>
              by_cases hf : funs s
              · exact absurd hty (awayNat_ne (h.leaves s hf ρ hρ hs) _)
              · have away := h.heads.other s isZ isS ρ (by simpa [termRows, hf] using hρ)
                simp only [offered, hs] at away
                exact absurd hty (awayNat_ne away _)
          | some p =>
              obtain ⟨ts, rfl⟩ := arrowSplit_head hs
              simp at hty
      · simp [undefinedDeriv, undefinedTy] at hty
  | .grounded g, _, ⟨d, hd, hm⟩ => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rw [sealedInfo_grounded] at hd
      rcases grounded_ty hd with rfl | ⟨c, hc, rfl⟩
      · simp [undefinedDeriv, undefinedTy] at hty
      · rcases hc with rfl | rfl | rfl <;> simp [classDeriv] at hty
  | .expression [], _, ⟨d, hd, hm⟩ => by
      obtain ⟨σ, -, hty⟩ := meets_iff.mp hm
      rcases mem_eff hd with hc | rfl
      · rw [sealedInfo_expression] at hc
        simp only [List.map_nil, nodeInfo, tupleTrees, tupleParts, Multiset.map_singleton,
          Multiset.mem_singleton] at hc
        subst hc
        simp at hty
      · simp [undefinedDeriv, undefinedTy] at hty
  | .expression (x :: xs), _, ⟨d, hd, hm⟩ => by
      obtain ⟨σ, hs, hty⟩ := meets_iff.mp hm
      rcases mem_eff hd with hc | rfl
      · rcases sealed_mem_expression_cands hc with hf | ht
        · obtain ⟨ρ, hρ, As, R, hsplit, hlen, E, hE, rfl⟩ := mem_funTrees hf
          simp only [Ty.bind_map] at hty
          rw [sealed_rows] at hρ
          match x, hρ with
          | .symbol s, hρ =>
              simp only at hρ
              by_cases isZ : s = "Z"
              · subst isZ
                rw [h.heads.zero, List.mem_singleton] at hρ
                subst hρ
                simp [arrowSplit] at hsplit
              by_cases isS : s = "S"
              · subst isS
                rw [h.heads.succ, List.mem_singleton] at hρ
                subst hρ
                simp only [arrowSplit_arrow, Option.some.injEq, Prod.mk.injEq] at hsplit
                obtain ⟨rfl, rfl⟩ := hsplit
                match xs, hlen with
                | [n], _ =>
                    right
                    refine ⟨n, rfl, ?_⟩
                    have hu : ¬ Unchecked (Ty.sym "Nat" : Ty String) := by simp [Unchecked]
                    rw [List.map_cons, List.map_nil, argEqs_cons_checked hu, Multiset.mem_bind] at hE
                    obtain ⟨dn, hdn, hE⟩ := hE
                    rw [argEqs, Multiset.map_singleton, Multiset.mem_singleton] at hE
                    subst hE
                    simp only [List.append_nil, solves_cons] at hs
                    obtain ⟨hn, hns⟩ := hs
                    refine ⟨dn, hdn, meets_of_pushed hns ?_⟩
                    rw [← hn]
                    simp
              · have away := h.heads.other s isZ isS ρ hρ
                simp only [offered, hsplit] at away
                exact absurd hty (awayNat_ne away _)
        · obtain ⟨dh, -, p, -, rfl⟩ := mem_tupleTrees_cons ht
          simp at hty
      · simp [undefinedDeriv, undefinedTy] at hty

/-- **A value typed at a sealed Peano sort is a Peano spine.** -/
theorem sealed_nat_spine_of_typable (h : SealedNatClosed Γ funs) (v : Atom) (hg : Ground v)
    (ht : STypable Γ funs v (.sym "Nat")) : NatSpine v := by
  induction hk : sizeOf v using Nat.strong_induction_on generalizing v with
  | _ k ih =>
      rcases sealed_nat_inversion h v hg ht with rfl | ⟨n, rfl, hn⟩
      · exact .zero
      · refine .succ n (ih (sizeOf n) ?_ n hg.2.1 hn rfl)
        subst hk
        simp
        omega

theorem sealed_nat_spine_of_count (h : SealedNatClosed Γ funs) (v : Atom) (hg : Ground v)
    (one : count (sealedInfo Γ funs v) (.sym "Nat") = 1) : NatSpine v :=
  sealed_nat_spine_of_typable h v hg ((stypable_iff_count Γ funs v _).mpr (by omega))

end SealedNat

/-! ## The pass without the cell test -/

section Trusted

/-- The operand of an expression read as a cell by position: the literal, or the
field at `item` where it is a machine integer. -/
def trustedOperand (s : Spec) (xs : List Atom) : Option ℤ :=
  match s.item with
  | none => some s.literal
  | some k => xs[k + 1]?.bind machineInt

/-- **The walk without the cell test**: every expression is read as a cell, its
recursive field at index `pre + 1` and its operand by position; anything else ends
the walk. No head, arity or end test. Where an index is out of range it answers
nothing (the pass that does not test the arity would read out of bounds there;
on a licensed argument it never does, `trustedOperands_build`). -/
def trustedOperands (s : Spec) : Atom → Option (List ℤ)
  | .expression xs =>
      match _h : xs[s.pre + 1]? with
      | none => none
      | some r => (trustedOperand s xs).bind fun x => (trustedOperands s r).map (x :: ·)
  | _ => some []
termination_by t => sizeOf t
decreasing_by
  have hmem : r ∈ xs := List.mem_of_getElem? _h
  have hlt := List.sizeOf_lt_of_mem hmem
  simp_wf
  omega

/-- One step of the walk without the cell test, where the recursive field is read. -/
theorem trustedOperands_expression (s : Spec) {xs : List Atom} {r : Atom} (h : xs[s.pre + 1]? = some r) :
    trustedOperands s (.expression xs) =
      (trustedOperand s xs).bind fun x => (trustedOperands s r).map (x :: ·) := by
  rw [trustedOperands]
  split
  · next h' => rw [h] at h'; cases h'
  · next r' h' =>
      rw [h] at h'
      cases h'
      rfl

/-- A value that is no expression ends the walk. -/
theorem trustedOperands_end (s : Spec) {t : Atom} (h : ∀ xs, t ≠ .expression xs) :
    trustedOperands s t = some [] := by
  unfold trustedOperands
  split
  · next xs => exact (h xs rfl).elim
  · rfl

/-- The recognized fold's value by the walk without the cell test. -/
def trustedRunFold (s : Spec) (t : Atom) : Option ℤ := (trustedOperands s t).bind s.runOperands

/-- **The machine's route without the cell test**: the fold where it answers, the
equations where it declines. -/
def trustedMachine (s : Spec) (E : Env) (n : ℕ) (t : Atom) : Multiset Atom :=
  match trustedRunFold s t with
  | some v => {RecognizedFolds.int v}
  | none => versionRun (s.body E) n [t]

/-- A spine of the fold's own cells ending in its `nil`. -/
inductive SpecSpine (s : Spec) : Atom → Prop
  | nil : SpecSpine s (.symbol s.nil)
  | cell (f : s.Fields) (r : Atom) : SpecSpine s r → SpecSpine s (s.cell f r)

theorem SpecSpine.build {s : Spec} {t : Atom} (h : SpecSpine s t) :
    ∃ fs : List s.Fields, t = s.family.build ⟨fs, .symbol s.nil⟩ := by
  induction h with
  | nil => exact ⟨[], rfl⟩
  | cell f r _ ih =>
      obtain ⟨fs, rfl⟩ := ih
      exact ⟨f :: fs, rfl⟩

theorem trustedOperand_cell (s : Spec) (wf : s.WF) (f : s.Fields) (r : Atom) :
    trustedOperand s (.symbol s.cons :: (f.1.1 ++ r :: f.1.2)) = s.operand f := by
  unfold trustedOperand Spec.operand
  cases hk : s.item with
  | none => rfl
  | some k =>
      simp only
      rw [List.getElem?_cons_succ, s.getElem?_fields f r (wf.item k hk).2]

theorem recursive_field (s : Spec) (f : s.Fields) (r : Atom) :
    (.symbol s.cons :: (f.1.1 ++ r :: f.1.2) : List Atom)[s.pre + 1]? = some r := by
  obtain ⟨⟨fs, gs⟩, hfs, hgs⟩ := f
  dsimp only at hfs ⊢
  rw [List.getElem?_cons_succ, List.getElem?_append_right (by omega), hfs, Nat.sub_self]
  rfl

theorem trustedOperands_cell (s : Spec) (wf : s.WF) (f : s.Fields) (r : Atom) :
    trustedOperands s (s.cell f r) =
      (s.operand f).bind fun x => (trustedOperands s r).map (x :: ·) := by
  rw [Spec.cell, trustedOperands_expression s (recursive_field s f r), trustedOperand_cell s wf]

/-- **On a spine of its own cells, the walk without the cell test reads exactly
what the tested walk reads.** -/
theorem trustedOperands_build (s : Spec) (wf : s.WF) :
    ∀ fs : List s.Fields, trustedOperands s (s.family.build ⟨fs, .symbol s.nil⟩) = fs.mapM s.operand
  | [] => by
      rw [Presentations.Family.build_nil, trustedOperands_end s (fun xs h => by cases h)]
      rfl
  | f :: fs => by
      rw [Presentations.Family.build_cons]
      change trustedOperands s (s.cell f _) = _
      rw [trustedOperands_cell s wf, trustedOperands_build s wf fs, List.mapM_cons]
      cases s.operand f with
      | none => rfl
      | some x =>
          cases fs.mapM s.operand with
          | none => rfl
          | some ys => rfl

/-- **Without the cell test the fold answers exactly as the recognized fold** on a
spine of its own cells, declines included. -/
theorem trustedRunFold_eq_runFold (s : Spec) (wf : s.WF) {t : Atom} (h : SpecSpine s t) :
    trustedRunFold s t = runFold s t := by
  obtain ⟨fs, rfl⟩ := h.build
  unfold trustedRunFold runFold
  rw [trustedOperands_build s wf fs, RecognizedFolds.readSpine_build s fs rfl, if_pos rfl]

/-- **The machine's route without the cell test has the equations' answers**, with
their multiplicities, on a spine of the fold's own cells, at every fuel past its
number of cells. -/
theorem trustedMachine_eq_equations (s : Spec) (wf : s.WF) (E : Env) (hE : PrimExact E s.op)
    {t : Atom} (h : SpecSpine s t) (n : ℕ) (hn : s.cells t < n) :
    trustedMachine s E n t = versionRun (s.body E) n [t] := by
  have same : trustedMachine s E n t = machine s E n t := by
    unfold trustedMachine machine
    rw [trustedRunFold_eq_runFold s wf h]
    cases runFold s t <;> rfl
  rw [same, RecognizedFolds.machine_eq_equations s wf E hE t n hn]

/-- A fold over `Nil` and `Cons`: cells `(Cons x r)`. -/
structure ListShape (s : Spec) : Prop where
  nil : s.nil = "Nil"
  cons : s.cons = "Cons"
  pre : s.pre = 1
  post : s.post = 0

/-- A fold over `Z` and `S`: cells `(S r)`. -/
structure NatShape (s : Spec) : Prop where
  nil : s.nil = "Z"
  cons : s.cons = "S"
  pre : s.pre = 0
  post : s.post = 0

theorem specSpine_of_consSpine (s : Spec) (hs : ListShape s) {P : Atom → Prop} :
    ∀ {v : Atom}, ConsSpine P v → SpecSpine s v
  | _, .nil => by
      have := SpecSpine.nil (s := s)
      rwa [hs.nil] at this
  | _, .cons x r _ hr => by
      have := SpecSpine.cell (s := s) ⟨([x], []), by simp [hs.pre], by simp [hs.post]⟩ r
        (specSpine_of_consSpine s hs hr)
      simpa [Spec.cell, hs.cons] using this

theorem specSpine_of_natSpine (s : Spec) (hs : NatShape s) : ∀ {v : Atom}, NatSpine v → SpecSpine s v
  | _, .zero => by
      have := SpecSpine.nil (s := s)
      rwa [hs.nil] at this
  | _, .succ n hn => by
      have := SpecSpine.cell (s := s) ⟨([], []), by simp [hs.pre], by simp [hs.post]⟩ n
        (specSpine_of_natSpine s hs hn)
      simpa [Spec.cell, hs.cons] using this

end Trusted

/-! ## The cell tests a sealed sort drops -/

section Drops

variable {Γ : Decls} {funs : String → Prop} [DecidablePred funs]

/-- **A fold over a sealed list sort may drop its cell test**: on a ground argument
the profile's relation types once at `(List τ)`, the machine's route without the
cell test has exactly the equations' answers. -/
theorem sealed_list_drop (h : SealedListClosed Γ funs) (τ : Ty Empty) (s : Spec) (hs : ListShape s)
    (wf : s.WF) (E : Env) (hE : PrimExact E s.op) {t : Atom} (hg : Ground t)
    (one : count (sealedInfo Γ funs t) (listOf τ) = 1) (n : ℕ) (hn : s.cells t < n) :
    trustedMachine s E n t = versionRun (s.body E) n [t] :=
  trustedMachine_eq_equations s wf E hE
    (specSpine_of_consSpine s hs (sealed_spine_of_count h τ t hg one)) n hn

/-- **A fold over a sealed Peano sort may drop its cell test.** -/
theorem sealed_nat_drop (h : SealedNatClosed Γ funs) (s : Spec) (hs : NatShape s) (wf : s.WF) (E : Env)
    (hE : PrimExact E s.op) {t : Atom} (hg : Ground t) (one : count (sealedInfo Γ funs t) (.sym "Nat") = 1)
    (n : ℕ) (hn : s.cells t < n) :
    trustedMachine s E n t = versionRun (s.body E) n [t] :=
  trustedMachine_eq_equations s wf E hE (specSpine_of_natSpine s hs (sealed_nat_spine_of_count h t hg one)) n hn

end Drops

/-! ## The profile's relation under functional declarations -/

section SealedFunctional

variable (Γ : Decls) (funs : String → Prop) [DecidablePred funs]

mutual
/-- **Every derivation the profile's relation records is satisfiable.** -/
theorem sealed_cands_sat : ∀ v : Atom, ∀ d ∈ (sealedInfo Γ funs v).cands, Sat d.eqs
  | .symbol s, d, hd => cands_sat Γ (.symbol s) d (by rw [← sealedInfo_symbol_cands Γ funs s]; exact hd)
  | .var x, d, hd => cands_sat Γ (.var x) d hd
  | .grounded g, d, hd => cands_sat Γ (.grounded g) d hd
  | .expression xs, d, hd => by
      rw [sealedInfo_expression] at hd
      exact nodeInfo_sat _ (sealed_effAll_sat xs) d hd

/-- The list version. -/
theorem sealed_effAll_sat : ∀ xs : List Atom, ∀ j ∈ xs.map (sealedInfo Γ funs), ∀ d ∈ eff j, Sat d.eqs
  | [], j, hj => absurd hj List.not_mem_nil
  | x :: xs, j, hj => by
      rw [List.map_cons, List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact eff_sat (sealed_cands_sat x)
      · exact sealed_effAll_sat xs j hj
end

variable {Γ funs}

theorem termRows_functional (hΓ : Functional Γ) : Functional (termRows Γ funs) := fun s => by
  unfold termRows
  split_ifs
  · simp
  · exact hΓ s

theorem sealed_rows_length_le_one (hΓ : Functional Γ) (v : Atom) :
    (sealedInfo Γ funs v).rows.length ≤ 1 := by
  rw [sealed_rows]
  cases v with
  | symbol s => exact termRows_functional hΓ s
  | var _ => simp
  | grounded _ => simp
  | expression _ => simp

mutual
/-- **Under functional declarations a value has at most one derivation** in the
profile's relation. -/
theorem sealed_card_cands_le_one (hΓ : Functional Γ) :
    ∀ v : Atom, Multiset.card (sealedInfo Γ funs v).cands ≤ 1
  | .symbol s => by
      rw [sealedInfo_symbol_cands]
      exact card_cands_le_one hΓ (.symbol s)
  | .var x => card_cands_le_one hΓ (.var x)
  | .grounded g => card_cands_le_one hΓ (.grounded g)
  | .expression [] => by
      rw [sealedInfo_expression]
      simp [nodeInfo, tupleTrees, tupleParts]
  | .expression (x :: xs) => by
      rw [sealedInfo_expression, List.map_cons]
      have all := sealed_card_effAll hΓ (x :: xs)
      simp only [nodeInfo]
      split_ifs
      · rw [tupleTrees, Multiset.card_map, card_tupleParts 0 _ (by simpa using all)]
      · exact card_funTrees_le_one _ _ (sealed_rows_length_le_one hΓ x)
          fun j hj => all j (by simp [hj])

/-- The list version. -/
theorem sealed_card_effAll (hΓ : Functional Γ) :
    ∀ xs : List Atom, ∀ j ∈ xs.map (sealedInfo Γ funs), Multiset.card (eff j) = 1
  | [], j, hj => absurd hj List.not_mem_nil
  | x :: xs, j, hj => by
      rw [List.map_cons, List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact card_eff_of_le_one (sealed_card_cands_le_one hΓ x)
      · exact sealed_card_effAll hΓ xs j hj
end

theorem sealed_card_eff (hΓ : Functional Γ) (v : Atom) :
    Multiset.card (eff (sealedInfo Γ funs v)) = 1 :=
  card_eff_of_le_one (sealed_card_cands_le_one hΓ v)

/-- The one effective derivation of a value in the profile's relation. -/
noncomputable def sealedDeriv (hΓ : Functional Γ) (v : Atom) : Deriv :=
  (Multiset.card_eq_one.mp (sealed_card_eff (funs := funs) hΓ v)).choose

theorem sealed_eff_deriv (hΓ : Functional Γ) (v : Atom) :
    eff (sealedInfo Γ funs v) = {sealedDeriv (funs := funs) hΓ v} :=
  (Multiset.card_eq_one.mp (sealed_card_eff (funs := funs) hΓ v)).choose_spec

theorem sealedDeriv_sat (hΓ : Functional Γ) (v : Atom) : Sat (sealedDeriv (funs := funs) hΓ v).eqs :=
  eff_sat (sealed_cands_sat Γ funs v) _ (by rw [sealed_eff_deriv hΓ v]; exact Multiset.mem_singleton_self _)

open Classical in
theorem sealed_count_eq_ite (hΓ : Functional Γ) (v : Atom) (T : Ty Empty) :
    count (sealedInfo Γ funs v) T =
      if Sat ((sealedDeriv (funs := funs) hΓ v).eqs ++ [((sealedDeriv (funs := funs) hΓ v).ty, T.lift)])
      then 1 else 0 := by
  unfold count
  rw [sealed_eff_deriv hΓ v, Multiset.filter_singleton]
  split_ifs <;> rfl

theorem sealed_count_le_one (hΓ : Functional Γ) (v : Atom) (T : Ty Empty) :
    count (sealedInfo Γ funs v) T ≤ 1 := by
  rw [sealed_count_eq_ite hΓ v T]
  split_ifs <;> omega

theorem sealed_forall₂_deriv (hΓ : Functional Γ) : ∀ vs : List Atom,
    List.Forall₂ (fun j d => eff j = {d}) (vs.map (sealedInfo Γ funs)) (vs.map (sealedDeriv (funs := funs) hΓ))
  | [] => .nil
  | v :: vs => .cons (sealed_eff_deriv hΓ v) (sealed_forall₂_deriv hΓ vs)

end SealedFunctional

/-! ## Constructors in the profile's relation -/

section SealedConstructors

theorem card_of_forall₂ : ∀ {js : List Info} {ds : List Deriv},
    List.Forall₂ (fun j d => eff j = {d}) js ds → ∀ j ∈ js, Multiset.card (eff j) = 1
  | [], [], .nil, _, hj => absurd hj List.not_mem_nil
  | _ :: _, _ :: _, .cons hd hrest, j, hj => by
      rw [List.mem_cons] at hj
      rcases hj with rfl | hj
      · rw [hd]
        rfl
      · exact card_of_forall₂ hrest j hj

open Classical in
/-- **The count of a constructor application at a closed named type**, whatever
records its fields have, as long as each contributes one derivation. -/
theorem count_ctor_node {Γ : Decls} {C : String} {As : List (Ty String)} {R : Ty String}
    (row : Γ C = [arrow As R]) (js : List Info) (ds : List Deriv)
    (hjs : List.Forall₂ (fun j d => eff j = {d}) js ds) (len : js.length = As.length)
    (T : Ty Empty) (hT : Named T) :
    count (nodeInfo (info Γ (.symbol C) :: js)) T =
      if Sat (ctorEqs 1 As ds ++ [(R.map DVar.own, T.lift)]) then 1 else 0 := by
  set E := ctorEqs 1 As ds with hEdef
  have args : argEqs 1 As js = {E} := argEqs_singletons 1 As _ _ (by simp [len]) hjs
  have funT : funTrees (info Γ (.symbol C)) js =
      (({(⟨R.map DVar.own, E⟩ : Deriv)} : Multiset Deriv)).filter fun d => Sat d.eqs := by
    unfold funTrees
    rw [info_symbol, row]
    simp only [Multiset.coe_singleton, Multiset.singleton_bind, arrowSplit_arrow, len, if_true, args,
      Multiset.map_singleton]
  by_cases hE : Sat E
  · have one : funTrees (info Γ (.symbol C)) js = {⟨R.map DVar.own, E⟩} := by
      rw [funT, Multiset.filter_singleton, if_pos hE]
    simp only [nodeInfo, one, Multiset.card_singleton, one_ne_zero, if_false]
    unfold count eff
    simp only [Multiset.card_singleton, one_ne_zero, if_false, Multiset.filter_singleton]
    split_ifs <;> rfl
  · have zero : funTrees (info Γ (.symbol C)) js = 0 := by
      rw [funT, Multiset.filter_singleton, if_neg hE]
      rfl
    simp only [nodeInfo, zero, Multiset.card_zero, if_true]
    rw [if_neg fun h => hE h.left]
    unfold count
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro d hd hsat
    have headCard : Multiset.card (eff (info Γ (.symbol C))) = 1 := by
      unfold eff
      rw [info_symbol, row]
      simp
    have hcard : Multiset.card (tupleTrees (info Γ (.symbol C) :: js)) ≠ 0 := by
      rw [tupleTrees, Multiset.card_map, card_tupleParts 0 _ (fun j hj => by
        rw [List.mem_cons] at hj
        rcases hj with rfl | hj
        · exact headCard
        · exact card_of_forall₂ hjs j hj)]
      exact one_ne_zero
    unfold eff at hd
    rw [if_neg hcard] at hd
    simp only [tupleTrees, Multiset.mem_map] at hd
    obtain ⟨p, hp, rfl⟩ := hd
    simp only [tupleParts, Multiset.mem_bind, Multiset.mem_map] at hp
    obtain ⟨d0, hd0, p', -, rfl⟩ := hp
    have hd0' : d0 = ⟨(arrow As R).map DVar.own, []⟩ := by
      unfold eff at hd0
      rw [info_symbol, row] at hd0
      simpa using hd0
    subst hd0'
    obtain ⟨ρ, hρ⟩ := hsat
    rw [solves_append, solves_singleton, Ty.lift_bind_ground] at hρ
    refine tuple_ne_named T hT _ ?_ _ ρ hρ.2
    simp only [Deriv.push, arrow, Ty.map_app, List.map_cons, Ty.map_sym]
    exact ⟨_, rfl⟩

variable {Γ : Decls} {funs : String → Prop} [DecidablePred funs]

/-- A constructor's application, in the profile's relation, reads the constructor's
rows as PeTTa's does. -/
theorem sealedInfo_ctor {C : String} (hc : ¬ funs C) (vs : List Atom) :
    sealedInfo Γ funs (.expression (.symbol C :: vs)) =
      nodeInfo (info Γ (.symbol C) :: vs.map (sealedInfo Γ funs)) := by
  rw [sealedInfo_expression, List.map_cons]
  congr 2
  simp [sealedInfo_symbol, info_symbol, termRows, hc]

open Classical in
theorem sealed_count_ctor (hΓ : Functional Γ) {C : String} (hc : ¬ funs C) {As : List (Ty String)}
    {R : Ty String} (row : Γ C = [arrow As R]) (vs : List Atom) (len : vs.length = As.length)
    (T : Ty Empty) (hT : Named T) :
    count (sealedInfo Γ funs (.expression (.symbol C :: vs))) T =
      if Sat (ctorEqs 1 As (vs.map (sealedDeriv (funs := funs) hΓ)) ++ [(R.map DVar.own, T.lift)])
      then 1 else 0 := by
  rw [sealedInfo_ctor hc]
  exact count_ctor_node row _ _ (sealed_forall₂_deriv hΓ vs) (by simp [len]) T hT

/-- **Inversion in the profile's relation**: a constructor's application typed once
at a closed named type comes from a match of the declared result, each checked
field typed once at its instance. -/
theorem sealed_ctor_inversion (hΓ : Functional Γ) {C : String} (hc : ¬ funs C)
    {As : List (Ty String)} {R : Ty String} (row : Γ C = [arrow As R]) (vs : List Atom)
    (len : vs.length = As.length) (T : Ty Empty) (hT : Named T)
    (typed : count (sealedInfo Γ funs (.expression (.symbol C :: vs))) T = 1) :
    ∃ σ : String → Ty Empty, R.bind σ = T ∧
      ∀ p ∈ List.zip As vs, ¬ Unchecked p.1 → count (sealedInfo Γ funs p.2) (p.1.bind σ) = 1 := by
  classical
  rw [sealed_count_ctor hΓ hc row vs len T hT] at typed
  split_ifs at typed with h
  obtain ⟨ρ, hρ⟩ := h
  rw [solves_append, solves_singleton] at hρ
  refine ⟨ρ ∘ DVar.own, ?_, ?_⟩
  · have := hρ.2
    rw [Ty.bind_map, Ty.lift_bind_ground] at this
    exact this
  · intro p hp hu
    have mem : (p.1, sealedDeriv (funs := funs) hΓ p.2) ∈ List.zip As (vs.map (sealedDeriv (funs := funs) hΓ)) := by
      rw [List.zip_map_right, List.mem_map]
      exact ⟨p, hp, rfl⟩
    have := ctorEqs_solves_fields ρ 1 As _ hρ.1 _ mem hu
    rw [sealed_count_eq_ite hΓ, if_pos this]

/-- **Construction in the profile's relation**: if every field that is not free is
typed once at its instance, the constructor's application is typed once at the
result's instance. -/
theorem sealed_ctor_construction (hΓ : Functional Γ) {C : String} (hc : ¬ funs C)
    {As : List (Ty String)} {R : Ty String} (row : Γ C = [arrow As R]) (hC : Constructor As R)
    (vs : List Atom) (len : vs.length = As.length) (σ : String → Ty Empty)
    (fields : ∀ p ∈ List.zip As vs, ¬ FreeField R p.1 → count (sealedInfo Γ funs p.2) (p.1.bind σ) = 1) :
    count (sealedInfo Γ funs (.expression (.symbol C :: vs))) (R.bind σ) = 1 := by
  classical
  rw [sealed_count_ctor hΓ hc row vs len _ (hC.named.bind σ), if_pos]
  have zipMem : ∀ p ∈ List.zip As (vs.map (sealedDeriv (funs := funs) hΓ)),
      ∃ v, p.2 = sealedDeriv (funs := funs) hΓ v ∧ (p.1, v) ∈ List.zip As vs := by
    intro p hp
    rw [List.zip_map_right, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact ⟨q.2, rfl, hq⟩
  obtain ⟨ρ, hρ, agree⟩ := ctorEqs_sat R σ 1 As (vs.map (sealedDeriv (funs := funs) hΓ)) hC.fields hC.distinct
    (fun p hp _ => by
      obtain ⟨v, hv, -⟩ := zipMem p hp
      rw [hv]
      exact sealedDeriv_sat hΓ v)
    (fun p hp hf => by
      obtain ⟨v, hv, hmem⟩ := zipMem p hp
      have := fields (p.1, v) hmem hf
      rw [sealed_count_eq_ite hΓ] at this
      split_ifs at this with h
      rw [hv]
      exact h)
  refine ⟨ρ, (solves_append _ _ _).mpr ⟨hρ, (solves_singleton _ _).mpr ?_⟩⟩
  rw [Ty.bind_map, Ty.lift_bind_ground]
  exact Ty.bind_congr R fun y hy => agree y hy

end SealedConstructors

/-! ## The producer's contract: versions prove their ranges in the profile's relation -/

section SealedVersions

variable (Γ : Decls) (funs : String → Prop) [DecidablePred funs] (grounded : String → Bool)

/-- **An entry fact in the profile's relation**: at a metatype name the guard
succeeds once, elsewhere the relation types the value once. -/
def SHolds (v : Atom) (T : Ty Empty) : Prop :=
  if MetaName T then guardCount (sealedInfo Γ funs v) T (metatype grounded v) = 1
  else count (sealedInfo Γ funs v) T = 1

/-- The entry facts of a closed row, in the profile's relation. -/
def SEntryFacts (As : List (Ty Empty)) (vs : List Atom) : Prop :=
  List.Forall₂ (fun A v => demand A.lift = .guarded → SHolds Γ funs grounded v A) As vs

/-- The entry facts of formals with type variables, in the profile's relation. -/
def SEntryPoly (Fs : List (Ty String)) (vs : List Atom) : Prop :=
  List.Forall₂ (fun F v => demand F = .guarded → ∃ τ : String → Ty Empty, SHolds Γ funs grounded v (F.bind τ))
    Fs vs

/-- Bindings meeting facts in the profile's relation. -/
def SMeetsFacts (Φ : String → Ty Empty → Prop) (ρ : List (String × Atom)) : Prop :=
  ∀ x U, Φ x U → ∃ w, ρ.lookup x = some w ∧ SHolds Γ funs grounded w U

variable (res : String → Ty Empty) (ent : String → List (Ty Empty))

/-- What a run assumes of the operations PeTTa provides and of the kept typed calls,
whose answers met their result guard in the profile's relation. -/
structure SEnvOK (E : Env) : Prop where
  prim : ∀ op vs c, primClass op vs.length = some c → ∀ r ∈ E.prim op vs, Literal c r
  kept : ∀ f vs, ∀ r ∈ E.kept f vs, SHolds Γ funs grounded r (res f)

/-- What a run assumes of its oracles, in the profile's relation. -/
structure SOracleOK (As : List (Ty String)) (R : Ty Empty) (O : Oracle) : Prop where
  self : ∀ ws, SEntryPoly Γ funs grounded As ws → ∀ r ∈ O.self ws, SHolds Γ funs grounded r R
  enter : ∀ f ws, SEntryFacts Γ funs grounded (ent f) ws → ∀ r ∈ O.enter f ws, SHolds Γ funs grounded r (res f)

/-- **The analysis' heads are constructors**: every pattern application is headed by
a symbol that is no function. The C reads patterns of data only. -/
def PatSafe : Pat → Prop
  | .var _ => True
  | .const _ => True
  | .ctor c ps => ¬ funs c ∧ ∀ p ∈ ps, PatSafe p
termination_by p => sizeOf p
decreasing_by
  have := List.sizeOf_lt_of_mem ‹_ ∈ ps›
  simp_wf
  omega

mutual
/-- **The analysis types data through constructors only**: every construction is
headed by a symbol that is no function (CeTTa plans an application of a function as
a call), and every constant has no held application of a function (the constants of
an equation's body are literals and symbols). -/
def ExprSafe : Expr → Prop
  | .var _ => True
  | .const a => NoHeldCalls funs a
  | .ctor c args => ¬ funs c ∧ ExprSafeAll args
  | .self args => ExprSafeAll args
  | .prim _ args => ExprSafeAll args
  | .call _ args => ExprSafeAll args
  | .enter _ args => ExprSafeAll args
  | .letE _ v b => ExprSafe v ∧ ExprSafe b
  | .ifE c t e => ExprSafe c ∧ ExprSafe t ∧ ExprSafe e
  | .empty => True
  | .caseE k _ bs => ExprSafe k ∧ ExprSafeAll bs
  | .matchE s _ t => ExprSafe s ∧ ExprSafe t

/-- The list version. -/
def ExprSafeAll : List Expr → Prop
  | [] => True
  | e :: es => ExprSafe e ∧ ExprSafeAll es
end

variable {Γ funs grounded res ent}

omit [DecidablePred funs] in
theorem exprSafeAll_mem : ∀ {es : List Expr}, ExprSafeAll funs es → ∀ e ∈ es, ExprSafe funs e
  | [], _, e, he => absurd he List.not_mem_nil
  | e' :: es, ⟨h, hs⟩, e, he => by
      rw [List.mem_cons] at he
      rcases he with rfl | he
      · exact h
      · exact exprSafeAll_mem hs e he

theorem SHolds.of_count {v : Atom} {T : Ty Empty} (h : count (sealedInfo Γ funs v) T = 1) :
    SHolds Γ funs grounded v T := by
  unfold SHolds
  split_ifs
  · unfold guardCount
    rw [if_neg (by omega), h]
  · exact h

theorem SHolds.count {v : Atom} {T : Ty Empty} (h : SHolds Γ funs grounded v T) (hm : ¬ MetaName T) :
    TypedCalls.count (sealedInfo Γ funs v) T = 1 := by
  unfold SHolds at h
  rwa [if_neg hm] at h

theorem sholds_literal {c : String} {r : Atom} (h : Literal c r) : SHolds Γ funs grounded r (.sym c) := by
  cases r with
  | grounded g =>
      refine SHolds.of_count ?_
      rw [sealedInfo_grounded, count_class Γ (show valueClass g = some c from h), if_pos rfl]
  | symbol _ => exact (h : False).elim
  | var _ => exact (h : False).elim
  | expression _ => exact (h : False).elim

theorem SMeetsFacts.extend {Φ : String → Ty Empty → Prop} {ρ ρ' : List (String × Atom)}
    (h : SMeetsFacts Γ funs grounded Φ ρ) (keep : ∀ x w, ρ.lookup x = some w → ρ'.lookup x = some w) :
    SMeetsFacts Γ funs grounded Φ ρ' :=
  fun x U hx => let ⟨w, hl, hw⟩ := h x U hx; ⟨w, keep x w hl, hw⟩

theorem sentryPoly_lift_iff (As : List (Ty Empty)) (vs : List Atom) :
    SEntryPoly Γ funs grounded (As.map Ty.lift) vs ↔ SEntryFacts Γ funs grounded As vs := by
  unfold SEntryPoly SEntryFacts
  rw [List.forall₂_map_left_iff]
  constructor
  · exact fun h => h.imp fun A v hA hg => by
      obtain ⟨τ, hτ⟩ := hA hg
      rwa [Ty.lift_bind_ground] at hτ
  · exact fun h => h.imp fun A v hv hg => ⟨fun _ => default, by rw [Ty.lift_bind_ground]; exact hv hg⟩

/-- **The facts read from a pattern hold in the profile's relation** of the bindings
of a value that meets the parameter's fact. -/
theorem sealed_patFact_sound (hΓ : Functional Γ) {p : Pat} {T : Ty Empty} {x : String} {U : Ty Empty}
    (h : PatFact Γ p T x U) :
    PatSafe funs p → ∀ {v : Atom} {ρ : List (String × Atom)} {w : Atom}, (Pat.vars p).Nodup →
      Pat.match p v = some ρ → SHolds Γ funs grounded v T → (x, w) ∈ ρ → SHolds Γ funs grounded w U := by
  induction h with
  | var x T =>
      intro _ v ρ w _ hm hv hw
      simp only [Pat.match, Option.some.injEq] at hm
      subst hm
      simp only [List.mem_singleton, Prod.mk.injEq, true_and] at hw
      subst hw
      exact hv
  | @ctor c Bs R ps T σ x U B p row cls len notMeta named hmatch field fixed inner ih =>
      intro safe v ρ w nodup hm hv hw
      rw [PatSafe] at safe
      match v, hm with
      | .expression (.symbol c' :: vs), hm =>
          simp only [Pat.match] at hm
          split_ifs at hm with hc
          subst hc
          have lenVs : vs.length = Bs.length := by
            rw [← Pat.matchAll_length ps vs ρ hm, len]
          obtain ⟨σ', hσ', fields⟩ :=
            sealed_ctor_inversion hΓ safe.1 row vs lenVs T named (hv.count notMeta)
          obtain ⟨v', ρ', hv', hm', hw'⟩ :=
            Pat.field_binding Bs ps vs ρ hm (by simpa [Pat.vars] using nodup) B p field
              (PatFact.mem_vars inner) hw
          have fixedB : ∀ y ∈ B.vars, y ∈ R.vars := by
            rcases cls.fields B (List.of_mem_zip field).1 with free | fixedB
            · exact absurd free fixed
            · exact fixedB
          have same : B.bind σ' = B.bind σ := fixed_instance_unique fixedB (hσ'.trans hmatch.symm)
          have typed := fields (B, v') hv' (checked_of_not_free fixed)
          rw [same] at typed
          have nodupPs : (Pat.varsAll ps).Nodup := by simpa [Pat.vars] using nodup
          exact ih (safe.2 p (List.of_mem_zip field).2)
            ((nodupPs.sublist (Pat.vars_sublist_varsAll (List.of_mem_zip field).2)))
            hm' (SHolds.of_count typed) hw'
      | .symbol _, hm => simp [Pat.match] at hm
      | .var _, hm => simp [Pat.match] at hm
      | .grounded _, hm => simp [Pat.match] at hm
      | .expression [], hm => simp [Pat.match] at hm
      | .expression (.var _ :: _), hm => simp [Pat.match] at hm
      | .expression (.grounded _ :: _), hm => simp [Pat.match] at hm
      | .expression (.expression _ :: _), hm => simp [Pat.match] at hm

variable {Φ : String → Ty Empty → Prop} {R : Ty Empty} {As : List (Ty String)} {E : Env}

mutual
/-- **The types the analysis gives hold of every value in the profile's relation**,
when the analysis types data through constructors only. -/
theorem sealed_eval_sound (hΓ : Functional Γ) (hE : SEnvOK Γ funs grounded res E) {O : Oracle}
    (hO : SOracleOK Γ funs grounded res ent As R O) :
    ∀ (e : Expr) (ρ : List (String × Atom)), SMeetsFacts Γ funs grounded Φ ρ → ExprSafe funs e →
      ∀ (T : Ty Empty), HasType Γ res Φ R e T → CallsOK Γ res ent Φ R As e →
        ∀ v ∈ e.eval E O ρ, SHolds Γ funs grounded v T
  | .var x, ρ, facts, _, T, h, _, v, hv => by
      cases h with
      | var hx =>
          obtain ⟨w, hl, hw⟩ := facts x T hx
          simp only [Expr.eval, hl, Multiset.mem_singleton] at hv
          subst hv
          exact hw
  | .const a, _, _, safe, T, h, _, v, hv => by
      cases h with
      | const hc =>
          simp only [Expr.eval, Multiset.mem_singleton] at hv
          subst hv
          refine SHolds.of_count ?_
          rw [sealed_count_eq Γ funs v (by simpa [ExprSafe] using safe)]
          exact hc
  | .ctor c args, ρ, facts, safe, T, h, hc, v, hv => by
      rw [ExprSafe] at safe
      cases h with
      | @ctor _ Bs R' _ σ row cls len notMeta parts =>
          cases hc with
          | ctor hargs =>
              simp only [Expr.eval, Multiset.mem_map] at hv
              obtain ⟨vs, hvs, rfl⟩ := hv
              have each := Expr.evalAll_mem E O ρ args vs hvs
              have lenVs : vs.length = Bs.length := by rw [← each.length_eq, len]
              refine SHolds.of_count (sealed_ctor_construction hΓ safe.1 row cls vs lenVs σ fun q hq hf => ?_)
              obtain ⟨e, he, hv⟩ := zip_of_forall₂ each Bs q.1 q.2 hq
              have mem : e ∈ args := (List.of_mem_zip he).2
              exact (List.forall_iff_forall_mem.mp (sealed_evalAll_sound hΓ hE hO args ρ facts) e mem
                (exprSafeAll_mem safe.2 e mem) (q.1.bind σ) (parts (q.1, e) he hf) (hargs e mem) q.2 hv).count
                (notMeta (q.1, e) he hf)
  | .self args, ρ, facts, safe, T, h, hc, v, hv => by
      rw [ExprSafe] at safe
      cases h with
      | self =>
          cases hc with
          | self hargs typed =>
              simp only [Expr.eval, Multiset.mem_bind] at hv
              obtain ⟨ws, hws, hv⟩ := hv
              exact hO.self ws (forall₂_compose typed (Expr.evalAll_mem E O ρ args ws hws)
                fun A e w he hA hw hg => by
                  obtain ⟨τ, hτ⟩ := hA hg
                  exact ⟨τ, List.forall_iff_forall_mem.mp
                    (sealed_evalAll_sound hΓ hE hO args ρ facts) e he (exprSafeAll_mem safe e he) _ hτ
                    (hargs e he) w hw⟩) v hv
  | .prim op args, ρ, _, _, T, h, _, v, hv => by
      cases h with
      | prim cls =>
          simp only [Expr.eval, Multiset.mem_bind] at hv
          obtain ⟨ws, hws, hv⟩ := hv
          have len : ws.length = args.length := (Expr.evalAll_mem E O ρ args ws hws).length_eq.symm
          exact sholds_literal (hE.prim op ws _ (by rw [len]; exact cls) v hv)
  | .call f args, ρ, _, _, T, h, _, v, hv => by
      cases h with
      | call =>
          simp only [Expr.eval, Multiset.mem_bind] at hv
          obtain ⟨ws, -, hv⟩ := hv
          exact hE.kept f ws v hv
  | .enter f args, ρ, facts, safe, T, h, hc, v, hv => by
      rw [ExprSafe] at safe
      cases h with
      | enter =>
          cases hc with
          | enter hargs typed =>
              simp only [Expr.eval, Multiset.mem_bind] at hv
              obtain ⟨ws, hws, hv⟩ := hv
              exact hO.enter f ws (forall₂_compose typed (Expr.evalAll_mem E O ρ args ws hws)
                fun A e w he hA hw hg => List.forall_iff_forall_mem.mp
                  (sealed_evalAll_sound hΓ hE hO args ρ facts) e he (exprSafeAll_mem safe e he) A (hA hg)
                  (hargs e he) w hw) v hv
  | .letE p val body, ρ, facts, safe, T, h, hc, v, hv => by
      rw [ExprSafe] at safe
      cases h with
      | letE hb =>
          cases hc with
          | letE _ hcb =>
              simp only [Expr.eval, Multiset.mem_bind] at hv
              obtain ⟨w, -, hv⟩ := hv
              split at hv
              · next ρ' hm =>
                  exact sealed_eval_sound hΓ hE hO body ρ'
                    (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx) safe.2 T hb hcb v hv
              · exact absurd hv (Multiset.notMem_zero v)
  | .ifE c t e, ρ, facts, safe, T, h, hc, v, hv => by
      rw [ExprSafe] at safe
      cases h with
      | ifE ht he =>
          cases hc with
          | ifE _ hct hce =>
              simp only [Expr.eval, Multiset.mem_bind] at hv
              obtain ⟨w, -, hv⟩ := hv
              split_ifs at hv
              · exact sealed_eval_sound hΓ hE hO t ρ facts safe.2.1 T ht hct v hv
              · exact sealed_eval_sound hΓ hE hO e ρ facts safe.2.2 T he hce v hv
  | .empty, _, _, _, _, _, _, v, hv => absurd hv (Multiset.notMem_zero v)
  | .caseE key pats bodies, ρ, facts, safe, T, h, hc, v, hv => by
      rw [ExprSafe] at safe
      cases h with
      | caseE hbs =>
          cases hc with
          | caseE _ hcbs =>
              simp only [Expr.eval, Multiset.mem_bind] at hv
              obtain ⟨w, -, hv⟩ := hv
              exact sealed_evalArms_sound hΓ hE hO w pats bodies ρ facts (exprSafeAll_mem safe.2) T hbs hcbs v hv
  | .matchE src p t, ρ, facts, safe, T, h, hc, v, hv => by
      rw [ExprSafe] at safe
      cases h with
      | matchE ht =>
          cases hc with
          | matchE _ hct =>
              simp only [Expr.eval, Multiset.mem_bind] at hv
              obtain ⟨sp, -, row, -, hv⟩ := hv
              split at hv
              · next ρ' hm =>
                  exact sealed_eval_sound hΓ hE hO t ρ'
                    (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx) safe.2 T ht hct v hv
              · exact absurd hv (Multiset.notMem_zero v)

/-- The list version. -/
theorem sealed_evalAll_sound (hΓ : Functional Γ) (hE : SEnvOK Γ funs grounded res E) {O : Oracle}
    (hO : SOracleOK Γ funs grounded res ent As R O) :
    ∀ (args : List Expr) (ρ : List (String × Atom)), SMeetsFacts Γ funs grounded Φ ρ →
      List.Forall (fun e => ExprSafe funs e → ∀ (T : Ty Empty), HasType Γ res Φ R e T →
        CallsOK Γ res ent Φ R As e → ∀ v ∈ e.eval E O ρ, SHolds Γ funs grounded v T) args
  | [], _, _ => trivial
  | e :: es, ρ, facts => (List.forall_cons _ e es).mpr
      ⟨sealed_eval_sound hΓ hE hO e ρ facts, sealed_evalAll_sound hΓ hE hO es ρ facts⟩

/-- The arms of a `case`. -/
theorem sealed_evalArms_sound (hΓ : Functional Γ) (hE : SEnvOK Γ funs grounded res E) {O : Oracle}
    (hO : SOracleOK Γ funs grounded res ent As R O) (w : Atom) :
    ∀ (pats : List Pat) (bodies : List Expr) (ρ : List (String × Atom)),
      SMeetsFacts Γ funs grounded Φ ρ → (∀ b ∈ bodies, ExprSafe funs b) →
      ∀ (T : Ty Empty), (∀ b ∈ bodies, HasType Γ res Φ R b T) →
      (∀ b ∈ bodies, CallsOK Γ res ent Φ R As b) →
      ∀ v ∈ Expr.evalArms E O ρ w pats bodies, SHolds Γ funs grounded v T
  | p :: ps, b :: bs, ρ, facts, safe, T, hbs, hcbs, v, hv => by
      simp only [Expr.evalArms] at hv
      split at hv
      · next ρ' hm =>
          exact sealed_eval_sound hΓ hE hO b ρ' (facts.extend fun x w hx => Pat.matchUnder_lookup hm hx)
            (safe b (by simp)) T (hbs b (by simp)) (hcbs b (by simp)) v hv
      · exact sealed_evalArms_sound hΓ hE hO w ps bs ρ facts (fun b' hb' => safe b' (by simp [hb'])) T
          (fun b' hb' => hbs b' (by simp [hb'])) (fun b' hb' => hcbs b' (by simp [hb'])) v hv
  | [], _, _, _, _, _, _, _, v, hv => by simp [Expr.evalArms] at hv
  | _ :: _, [], _, _, _, _, _, _, v, hv => by simp [Expr.evalArms] at hv
end

/-- **The facts an accepted equation reads hold in the profile's relation** of the
bindings of arguments meeting its entry facts there. -/
theorem sealed_eqFacts_sound (hΓ : Functional Γ) {Cs : List (Ty Empty)} {eq : Equation}
    (linear : (Pat.varsAll eq.pats).Nodup) (patSafe : ∀ p ∈ eq.pats, PatSafe funs p)
    {vs : List Atom} {ρ : List (String × Atom)} (hm : Pat.matchAll eq.pats vs = some ρ)
    (hvs : SEntryFacts Γ funs grounded Cs vs) : SMeetsFacts Γ funs grounded (eqFacts Γ Cs eq) ρ := by
  rintro x U ⟨A, p, hAp, hg, hpf⟩
  have key : x ∈ ρ.map Prod.fst := by
    rw [Pat.matchAll_keys _ _ _ hm]
    exact Pat.vars_subset_varsAll (List.of_mem_zip hAp).2 hpf.mem_vars
  obtain ⟨w, hl⟩ := lookup_of_mem_keys ρ x key
  refine ⟨w, hl, ?_⟩
  have hw : (x, w) ∈ ρ := by
    obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp hl
    simp
  obtain ⟨v, ρ', hv, hm', hw'⟩ := Pat.field_binding Cs eq.pats vs ρ hm linear A p hAp
    hpf.mem_vars hw
  exact sealed_patFact_sound hΓ hpf (patSafe p (List.of_mem_zip hAp).2)
    (linear.sublist (Pat.vars_sublist_varsAll (List.of_mem_zip hAp).2)) hm'
    (forall₂_zip hvs A v hv hg) hw'

/-- **The version of an accepted relation proves its range in the profile's
relation** (`petta_range`): on arguments meeting the entry facts there, every
answer of its run, at every fuel, meets its result's fact there, when the analysis
types data through constructors only and the callees it enters answer their
results' facts. -/
theorem sealed_version_results (hΓ : Functional Γ) {Cs : List (Ty Empty)} {eqs : List Equation}
    (acc : ∀ eq ∈ eqs, Accepted Γ res ent Cs R eq)
    (safe : ∀ eq ∈ eqs, ExprSafe funs eq.rhs ∧ ∀ p ∈ eq.pats, PatSafe funs p)
    (hE : SEnvOK Γ funs grounded res E) (enV : String → List Atom → Multiset Atom)
    (enRes : ∀ f ws, SEntryFacts Γ funs grounded (ent f) ws → ∀ r ∈ enV f ws, SHolds Γ funs grounded r (res f)) :
    ∀ n vs, SEntryFacts Γ funs grounded Cs vs →
      ∀ r ∈ versionRun (fun o => equationsBody E eqs ⟨o, enV⟩) n vs, SHolds Γ funs grounded r R
  | 0, _, _, r, hr => absurd hr (Multiset.notMem_zero r)
  | n + 1, vs, hvs, r, hr => by
      have ih := sealed_version_results hΓ acc safe hE enV enRes n
      simp only [versionRun] at hr
      unfold equationsBody at hr
      obtain ⟨eq, heq, hr⟩ := Multiset.mem_bind.mp hr
      split at hr
      · next ρ hm =>
          exact sealed_eval_sound hΓ hE
            ⟨fun ws hws => ih ws ((sentryPoly_lift_iff Cs ws).mp hws), enRes⟩
            eq.rhs ρ (sealed_eqFacts_sound hΓ (acc eq heq).linear (safe eq heq).2 hm hvs)
            (safe eq heq).1 R (acc eq heq).result (acc eq heq).calls r hr
      · exact absurd hr (Multiset.notMem_zero r)

end SealedVersions

/-! ## The modular drop -/

section Modular

variable {Γ : Decls} {funs : String → Prop} [DecidablePred funs] {grounded : String → Bool}
  {res : String → Ty Empty} {ent : String → List (Ty Empty)} {E : Env}

/-- **A typed producer's ground answers are spines** of a sealed list sort: an
accepted producer whose range is `(List τ)` answers, on arguments meeting its entry
facts in the profile's relation, values typed once there, which are spines. The
consumer needs no analysis of the producer. -/
theorem producer_answers_spines (h : SealedListClosed Γ funs) (hΓ : Functional Γ) (τ : Ty Empty)
    {Cs : List (Ty Empty)} {eqs : List Equation}
    (acc : ∀ eq ∈ eqs, Accepted Γ res ent Cs (listOf τ) eq)
    (safe : ∀ eq ∈ eqs, ExprSafe funs eq.rhs ∧ ∀ p ∈ eq.pats, PatSafe funs p)
    (hE : SEnvOK Γ funs grounded res E) (enV : String → List Atom → Multiset Atom)
    (enRes : ∀ f ws, SEntryFacts Γ funs grounded (ent f) ws → ∀ r ∈ enV f ws, SHolds Γ funs grounded r (res f))
    (n : ℕ) (vs : List Atom) (hvs : SEntryFacts Γ funs grounded Cs vs)
    {r : Atom} (hr : r ∈ versionRun (fun o => equationsBody E eqs ⟨o, enV⟩) n vs) (hg : Ground r) :
    ConsSpine (fun _ => True) r := by
  have holds := sealed_version_results hΓ acc safe hE enV enRes n vs hvs r hr
  have notMeta : ¬ MetaName (listOf τ) := by simp [MetaName, listOf]
  exact sealedLicensed_of_closed h τ r hg (holds.count notMeta)

/-- **The modular cell-test drop**: a fold over a sealed list sort, called on a
ground answer of an accepted producer at that sort, runs without its cell test
and has exactly the equations' answers. -/
theorem modular_list_drop (h : SealedListClosed Γ funs) (hΓ : Functional Γ) (τ : Ty Empty)
    {Cs : List (Ty Empty)} {eqs : List Equation}
    (acc : ∀ eq ∈ eqs, Accepted Γ res ent Cs (listOf τ) eq)
    (safe : ∀ eq ∈ eqs, ExprSafe funs eq.rhs ∧ ∀ p ∈ eq.pats, PatSafe funs p)
    (hE : SEnvOK Γ funs grounded res E) (enV : String → List Atom → Multiset Atom)
    (enRes : ∀ f ws, SEntryFacts Γ funs grounded (ent f) ws → ∀ r ∈ enV f ws, SHolds Γ funs grounded r (res f))
    (n : ℕ) (vs : List Atom) (hvs : SEntryFacts Γ funs grounded Cs vs)
    {r : Atom} (hr : r ∈ versionRun (fun o => equationsBody E eqs ⟨o, enV⟩) n vs) (hg : Ground r)
    (s : Spec) (hs : ListShape s) (wf : s.WF) (E' : Env) (hE' : PrimExact E' s.op) (m : ℕ) (hm : s.cells r < m) :
    trustedMachine s E' m r = versionRun (s.body E') m [r] :=
  trustedMachine_eq_equations s wf E' hE'
    (specSpine_of_consSpine s hs (producer_answers_spines h hΓ τ acc safe hE enV enRes n vs hvs hr hg)) m hm

/-- **A typed producer's ground answers are Peano spines** of a sealed Peano sort. -/
theorem producer_answers_nat_spines (h : SealedNatClosed Γ funs) (hΓ : Functional Γ)
    {Cs : List (Ty Empty)} {eqs : List Equation}
    (acc : ∀ eq ∈ eqs, Accepted Γ res ent Cs (.sym "Nat") eq)
    (safe : ∀ eq ∈ eqs, ExprSafe funs eq.rhs ∧ ∀ p ∈ eq.pats, PatSafe funs p)
    (hE : SEnvOK Γ funs grounded res E) (enV : String → List Atom → Multiset Atom)
    (enRes : ∀ f ws, SEntryFacts Γ funs grounded (ent f) ws → ∀ r ∈ enV f ws, SHolds Γ funs grounded r (res f))
    (n : ℕ) (vs : List Atom) (hvs : SEntryFacts Γ funs grounded Cs vs)
    {r : Atom} (hr : r ∈ versionRun (fun o => equationsBody E eqs ⟨o, enV⟩) n vs) (hg : Ground r) :
    NatSpine r := by
  have holds := sealed_version_results hΓ acc safe hE enV enRes n vs hvs r hr
  have notMeta : ¬ MetaName (.sym "Nat") := by simp [MetaName]
  exact sealed_nat_spine_of_count h r hg (holds.count notMeta)

/-- **The modular cell-test drop over a sealed Peano sort.** -/
theorem modular_nat_drop (h : SealedNatClosed Γ funs) (hΓ : Functional Γ)
    {Cs : List (Ty Empty)} {eqs : List Equation}
    (acc : ∀ eq ∈ eqs, Accepted Γ res ent Cs (.sym "Nat") eq)
    (safe : ∀ eq ∈ eqs, ExprSafe funs eq.rhs ∧ ∀ p ∈ eq.pats, PatSafe funs p)
    (hE : SEnvOK Γ funs grounded res E) (enV : String → List Atom → Multiset Atom)
    (enRes : ∀ f ws, SEntryFacts Γ funs grounded (ent f) ws → ∀ r ∈ enV f ws, SHolds Γ funs grounded r (res f))
    (n : ℕ) (vs : List Atom) (hvs : SEntryFacts Γ funs grounded Cs vs)
    {r : Atom} (hr : r ∈ versionRun (fun o => equationsBody E eqs ⟨o, enV⟩) n vs) (hg : Ground r)
    (s : Spec) (hs : NatShape s) (wf : s.WF) (E' : Env) (hE' : PrimExact E' s.op) (m : ℕ) (hm : s.cells r < m) :
    trustedMachine s E' m r = versionRun (s.body E') m [r] :=
  trustedMachine_eq_equations s wf E' hE'
    (specSpine_of_natSpine s hs (producer_answers_nat_spines h hΓ acc safe hE enV enRes n vs hvs hr hg)) m hm

end Modular

/-! ## Controls -/

namespace Controls

open TypedCalls.Controls (sym num app)
open CertifiedSpines.Controls (listNum count_int count_nil_of)
open TypedFoldBound.Controls (listTDecls listTFuns heldBuild listTDecls_functional numRow eqRow buildRow sumRow)

/-- `list_T`'s sort is sealed-closed: its functions, `build` and `sum`, have arrow
rows only. -/
theorem sealed_listT_closed : SealedListClosed listTDecls listTFuns :=
  ⟨TypedFoldBound.Controls.sealed_listT, fun s hs ρ hρ hsplit => by
    simp only [listTFuns] at hs
    rcases hs with rfl | rfl <;> simp [listTDecls] at hρ <;> subst hρ <;> simp [arrowSplit_arrow] at hsplit⟩

theorem sealed_listT_licensed : SealedLicensed listTDecls listTFuns (.sym "Number") :=
  sealedLicensed_of_closed sealed_listT_closed _

/-- **e02's typing**: the held `(build 1 Nil)` is typed once at `(List Number)` by
PeTTa's relation and not by the profile's. -/
theorem held_build_stable_vs_sealed :
    count (info listTDecls heldBuild) listNum = 1 ∧
      count (sealedInfo listTDecls listTFuns heldBuild) listNum ≠ 1 :=
  ⟨TypedFoldBound.Controls.held_build_certified.1, fun one =>
    TypedFoldBound.Controls.held_build_certified.2.2.1
      (sealed_listT_licensed heldBuild TypedFoldBound.Controls.held_build_certified.2.1 one)⟩

/-- `(Cons 1 Nil)`. -/
def consOne : Atom := app "Cons" [num 1, sym "Nil"]

theorem consOne_noHeldCalls : NoHeldCalls listTFuns consOne := by
  simp [consOne, app, sym, num, NoHeldCalls, NoHeldCallsAll, HeadFreeList, HeadFree, listTFuns]

/-- **e03's typing**: a constructor term is typed once at `(List Number)` by both
relations. -/
theorem cons_typed_both :
    count (info listTDecls consOne) listNum = 1 ∧
      count (sealedInfo listTDecls listTFuns consOne) listNum = 1 := by
  have stable : count (info listTDecls consOne) listNum = 1 := by
    have := ctor_construction listTDecls_functional (C := "Cons") (by simp [listTDecls])
      cons_constructor [num 1, sym "Nil"] rfl (fun _ => .sym "Number") (by
        intro p hp _
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
          or_false] at hp
        rcases hp with rfl | rfl
        · exact count_int _ 1
        · simpa [listOf] using count_nil_of listTDecls_functional (by simp [listTDecls]) (.sym "Number"))
    simpa [consOne, listOf] using this
  exact ⟨stable, by rw [sealed_count_eq listTDecls listTFuns consOne consOne_noHeldCalls]; exact stable⟩

/-- **Without the cell test the held `(build 1 Nil)` is read as a cell**: the pass
answers `1`, where the recognized fold of `sum` and its equations answer nothing.
This is why only a licensed argument may take it. -/
theorem held_build_trusted_wrong :
    trustedRunFold RecognizedFolds.Controls.sumSpec heldBuild = some 1 ∧
      runFold RecognizedFolds.Controls.sumSpec heldBuild = none := by
  constructor
  · have step : trustedOperands RecognizedFolds.Controls.sumSpec heldBuild = some [1] := by
      rw [heldBuild, app, trustedOperands_expression _ (r := sym "Nil") rfl,
        trustedOperands_end _ (fun xs h => by cases h)]
      decide
    rw [trustedRunFold, step]
    decide
  · unfold runFold Spec.readSpine
    rw [Presentations.Family.spine_of_none _ (show RecognizedFolds.Controls.sumSpec.uncell heldBuild = none from rfl)]
    simp [heldBuild, app, sym]

/-- **The end test matters too**: `(Cons 1 Foo)` is read as `1` without the cell
test, where the recognized fold declines. -/
theorem improper_end_trusted :
    trustedRunFold RecognizedFolds.Controls.sumSpec
        (RecognizedFolds.Controls.spineOf [RecognizedFolds.int 1] (.symbol "Foo")) = some 1 ∧
      runFold RecognizedFolds.Controls.sumSpec
        (RecognizedFolds.Controls.spineOf [RecognizedFolds.int 1] (.symbol "Foo")) = none := by
  constructor
  · have step : trustedOperands RecognizedFolds.Controls.sumSpec
        (RecognizedFolds.Controls.spineOf [RecognizedFolds.int 1] (.symbol "Foo")) = some [1] := by
      rw [RecognizedFolds.Controls.spineOf, List.map_cons, List.map_nil,
        Presentations.Family.build_cons, Presentations.Family.build_nil]
      change trustedOperands RecognizedFolds.Controls.sumSpec
        (RecognizedFolds.Controls.sumSpec.cell _ _) = _
      rw [trustedOperands_cell _ RecognizedFolds.Controls.sumSpec_wf,
        trustedOperands_end _ (fun xs h => by cases h)]
      decide
    rw [trustedRunFold, step]
    decide
  · unfold runFold RecognizedFolds.Controls.spineOf
    rw [RecognizedFolds.readSpine_build RecognizedFolds.Controls.sumSpec _ RecognizedFolds.Controls.foo_end]
    rfl

/-- The declarations of a program with a declared second list constructor `pair`
and no equations for it. -/
def pairDecls : Decls := fun s => if s = "pair" then [buildRow] else listTDecls s

/-- **A declared constructor is part of its sort** (e06): `pair` is no function, its
row offers `(List Number)`, and the sort is not sealed-closed, so a fold keeps its
cell test. -/
theorem pair_opens : ¬ SealedListClosed pairDecls listTFuns := fun h => by
  have := h.heads.other "pair" (by decide) (by decide) buildRow (by simp [termRows, listTFuns, pairDecls])
  simp [offered, AwayFromList, buildRow, listOf] at this

/-- `inc : (-> Number Number)`, a function. -/
abbrev incRow : Ty String := arrow [.sym "Number"] (.sym "Number")

def incDecls : Decls := fun s => if s = "inc" then [incRow] else []

def incFuns (s : String) : Prop := s = "inc"

instance : DecidablePred incFuns := fun s => by unfold incFuns; infer_instance

/-- **A function's name keeps its arrow type** in the profile's relation, so a typed
higher-order call such as `(app1 inc 3)` checks as before (e15, e16); `termRows`
alone would lose it. -/
theorem function_value_typed :
    count (sealedInfo incDecls incFuns (sym "inc")) (arrow [.sym "Number"] (.sym "Number")) = 1 ∧
      count (info (termRows incDecls incFuns) (sym "inc")) (arrow [.sym "Number"] (.sym "Number")) = 0 := by
  have lifted : (incRow : Ty String) = (arrow [.sym "Number"] (.sym "Number") : Ty Empty).lift := by
    simp [incRow, arrow, Ty.lift, Ty.map]
  constructor
  · have := count_symbol_closed incDecls "inc" (arrow [.sym "Number"] (.sym "Number"))
      (by simp [incDecls, lifted]) (arrow [.sym "Number"] (.sym "Number"))
    rw [if_pos rfl] at this
    unfold count at this ⊢
    rw [eff_eq_of_cands (sealedInfo_symbol_cands incDecls incFuns "inc")]
    exact this
  · classical
    have none : termRows incDecls incFuns "inc" = [] := by simp [termRows, incFuns]
    unfold count
    rw [info_symbol, none]
    unfold eff
    simp only [List.map_nil, Multiset.coe_nil, Multiset.card_zero, if_true, Multiset.filter_singleton]
    rw [if_neg]
    · rfl
    · rintro ⟨σ, hσ⟩
      rw [solves_append, solves_singleton, Ty.lift_bind_ground] at hσ
      have := hσ.2
      simp [undefinedDeriv, undefinedTy, arrow] at this

/-! ### The whole chain on `build` and `sum` -/

/-- `build : (-> Number (List Number) (List Number))` beside the probe declarations. -/
def buildDecls : Decls := fun s => if s = "build" then [buildRow] else TypedCalls.Controls.decls s

/-- `build` has equations; the probe declarations' other symbols have none. -/
def buildFuns (s : String) : Prop := s = "build"

instance : DecidablePred buildFuns := fun s => by unfold buildFuns; infer_instance

theorem buildDecls_functional : Functional buildDecls := by
  intro s
  unfold buildDecls
  split_ifs
  · simp
  · exact TypedCalls.Controls.decls_functional s

/-- `(= (build $n $acc) (if (== $n 0) $acc (build (- $n 1) (Cons $n $acc))))`. -/
def buildEqs : List Equation :=
  [⟨[.var "n", .var "acc"],
    .ifE (.prim "==" [.var "n", .const (num 0)]) (.var "acc")
      (.self [.prim "-" [.var "n", .const (num 1)], .ctor "Cons" [.var "n", .var "acc"]])⟩]

/-- **The analysis accepts `build`**: `$acc` is a `(List Number)`, the call to itself
meets the formals, `(Cons $n $acc)` by `Cons`'s row, and the result is `$acc` or
the call to itself. -/
theorem build_accepted (res : String → Ty Empty) (ent : String → List (Ty Empty)) :
    ∀ eq ∈ buildEqs, Accepted buildDecls res ent [.sym "Number", listNum] listNum eq := by
  intro eq heq
  simp only [buildEqs, List.mem_singleton] at heq
  subst heq
  have nFact : eqFacts buildDecls [.sym "Number", listNum]
      ⟨[.var "n", .var "acc"], .ifE (.prim "==" [.var "n", .const (num 0)]) (.var "acc")
        (.self [.prim "-" [.var "n", .const (num 1)], .ctor "Cons" [.var "n", .var "acc"]])⟩
      "n" (.sym "Number") :=
    ⟨.sym "Number", .var "n", by simp, by decide, PatFact.var _ _⟩
  have accFact : eqFacts buildDecls [.sym "Number", listNum]
      ⟨[.var "n", .var "acc"], .ifE (.prim "==" [.var "n", .const (num 0)]) (.var "acc")
        (.self [.prim "-" [.var "n", .const (num 1)], .ctor "Cons" [.var "n", .var "acc"]])⟩
      "acc" listNum :=
    ⟨listNum, .var "acc", by simp, by decide, PatFact.var _ _⟩
  have inst : ((listOf (Ty.var "a") : Ty String).bind fun _ => Ty.sym "Number") = listNum := by
    simp [listOf, listNum]
  have consTyped : HasType buildDecls res
      (eqFacts buildDecls [.sym "Number", listNum]
        ⟨[.var "n", .var "acc"], .ifE (.prim "==" [.var "n", .const (num 0)]) (.var "acc")
          (.self [.prim "-" [.var "n", .const (num 1)], .ctor "Cons" [.var "n", .var "acc"]])⟩)
      listNum (.ctor "Cons" [.var "n", .var "acc"]) listNum := by
    rw [← inst]
    refine HasType.ctor (σ := fun _ => .sym "Number") (by simp [buildDecls, TypedCalls.Controls.cons_row])
      cons_constructor rfl ?_ ?_
    · intro q hq _
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
        or_false] at hq
      rcases hq with rfl | rfl <;> simp [MetaName, listOf]
    · intro q hq _
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
        or_false] at hq
      rcases hq with rfl | rfl
      · exact .var nFact
      · simpa [listOf, listNum] using (HasType.var accFact : HasType buildDecls res _ listNum _ listNum)
  refine ⟨by simp [Pat.varsAll, Pat.vars], rfl, ?_, .ifE (.var accFact) .self⟩
  refine .ifE (.prim fun e he => ?_) .var (CallsOK.selfClosed (fun e he => ?_) (.cons (.prim rfl) (.cons consTyped .nil)))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact .var
    · exact .const
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact .prim fun e he => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact .var
        · exact .const
    · exact .ctor fun e he => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> exact .var

/-- `build`'s equations build data through `Cons` only, which is no function. -/
theorem build_safe : ∀ eq ∈ buildEqs, ExprSafe buildFuns eq.rhs ∧ ∀ p ∈ eq.pats, PatSafe buildFuns p := by
  intro eq heq
  simp only [buildEqs, List.mem_singleton] at heq
  subst heq
  refine ⟨?_, ?_⟩
  · simp [ExprSafe, ExprSafeAll, NoHeldCalls, buildFuns]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [PatSafe]

/-- The probe's operations answer their classes, in the profile's relation too. -/
theorem senv_ok (grounded : String → Bool) (res : String → Ty Empty) :
    SEnvOK buildDecls buildFuns grounded res TypedCalls.Controls.env where
  prim := (TypedCalls.Controls.env_ok (Γ := buildDecls) grounded res).prim
  kept _ _ r hr := absurd hr (Multiset.notMem_zero r)

/-- `build`'s list sort is sealed-closed. -/
theorem build_closed : SealedListClosed buildDecls buildFuns := by
  refine sealedListClosed_of (by simp [buildDecls, TypedCalls.Controls.decls])
    (by simp [buildDecls, TypedCalls.Controls.cons_row]) (by simp [buildFuns]) (by simp [buildFuns])
    (fun s hs h1 h2 ρ hρ => ?_) (fun s hs ρ hρ hsplit => ?_)
  · simp only [buildFuns] at hs
    unfold buildDecls TypedCalls.Controls.decls at hρ
    split_ifs at hρ <;> simp_all [offered, AwayFromList]
  · simp only [buildFuns] at hs
    subst hs
    simp only [buildDecls, if_true, List.mem_singleton] at hρ
    subst hρ
    simp [arrowSplit_arrow] at hsplit

/-- `build`'s equations with the probe's operations and no callee. -/
abbrev buildBody : (List Atom → Multiset Atom) → List Atom → Multiset Atom :=
  fun o => equationsBody TypedCalls.Controls.env buildEqs ⟨o, TypedCalls.Controls.noCallee⟩

/-- **`build`'s ground answers are spines**, from its declaration alone: its version
proves its range in the profile's relation, and the sort is sealed-closed. -/
theorem build_answers_spines (grounded : String → Bool) (n : ℕ) (vs : List Atom)
    (hvs : SEntryFacts buildDecls buildFuns grounded [.sym "Number", listNum] vs)
    {r : Atom} (hr : r ∈ versionRun buildBody n vs) (hg : Ground r) : ConsSpine (fun _ => True) r :=
  producer_answers_spines (res := TypedCalls.Controls.noRes) (ent := TypedCalls.Controls.noEnt)
    build_closed buildDecls_functional (.sym "Number") (build_accepted _ _) build_safe
    (senv_ok grounded _) TypedCalls.Controls.noCallee (fun _ _ _ r hr => absurd hr (Multiset.notMem_zero r))
    n vs hvs hr hg

/-- `(build 3 Nil)` meets `build`'s entry facts in the profile's relation. -/
theorem build3_entry (grounded : String → Bool) :
    SEntryFacts buildDecls buildFuns grounded [.sym "Number", listNum] [num 3, sym "Nil"] := by
  refine .cons (fun _ => SHolds.of_count ?_) (.cons (fun _ => SHolds.of_count ?_) .nil)
  · rw [sealedInfo_grounded]
    exact count_int _ 3
  · rw [sealed_count_eq buildDecls buildFuns (sym "Nil") trivial]
    simpa [listOf, listNum] using count_nil_of buildDecls_functional
      (by simp [buildDecls, TypedCalls.Controls.decls]) (.sym "Number")

/-- **`(sum (build 3 Nil))` without the cell test**: on every ground answer of
`(build 3 Nil)`, the fold of `sum` without its cell test has exactly the
equations' answers. -/
theorem sum_build_drop (grounded : String → Bool) (n : ℕ) {r : Atom}
    (hr : r ∈ versionRun buildBody n [num 3, sym "Nil"]) (hg : Ground r) (m : ℕ)
    (hm : RecognizedFolds.Controls.sumSpec.cells r < m) :
    trustedMachine RecognizedFolds.Controls.sumSpec TypedCalls.Controls.env m r =
      versionRun (RecognizedFolds.Controls.sumSpec.body TypedCalls.Controls.env) m [r] :=
  trustedMachine_eq_equations _ RecognizedFolds.Controls.sumSpec_wf _ RecognizedFolds.Controls.plus_exact
    (specSpine_of_consSpine _ ⟨rfl, rfl, rfl, rfl⟩ (build_answers_spines grounded n _ (build3_entry grounded) hr hg))
    m hm

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SealedSorts
