import Mettapedia.Computability.Coded
import Mathlib.Computability.RE

/-!
# Relations decidable or enumerable on codes

A relation between coded types is **decidable on codes** when a computable test
on pairs of numbers agrees with it on codes, and **enumerable on codes** when a
recursively enumerable relation on pairs of numbers does (`DecidableOnCodes`,
`EnumerableOnCodes`).

For types coded by Mathlib's own encodings these are Mathlib's computable and
recursively enumerable predicates (`decidableOnCodes_iff`,
`enumerableOnCodes_iff`), and a function computable on codes is computable
(`CodeComputable.computable`). So Mathlib's notions are the instance of these
at its encodings.

A relation is enumerable on codes when a function computable on codes lists,
for a bound and a first argument, finitely many second arguments, every
related one at some bound, and distinct values have distinct codes
(`enumerableOnCodes_of_bounded`).
-/

set_option autoImplicit false

namespace Mettapedia.Computability

section Relations

variable {α β : Type} [Coded α] [Coded β]

/-- **Decidable on codes**: a computable test on pairs of numbers agrees with the relation on codes. -/
def DecidableOnCodes (R : α → β → Prop) : Prop :=
  ∃ test : ℕ × ℕ → Bool, Computable test ∧ ∀ a b, test (code a, code b) = true ↔ R a b

/-- **Enumerable on codes**: a recursively enumerable relation on pairs of numbers agrees with the relation on
codes. -/
def EnumerableOnCodes (R : α → β → Prop) : Prop :=
  ∃ listed : ℕ × ℕ → Prop, REPred listed ∧ ∀ a b, listed (code a, code b) ↔ R a b

theorem DecidableOnCodes.enumerable {R : α → β → Prop} (decidable : DecidableOnCodes R) :
    EnumerableOnCodes R := by
  obtain ⟨test, computable, agrees⟩ := decidable
  exact ⟨fun p => test p = true, (ComputablePred.computable_iff.mpr ⟨test, computable, rfl⟩).to_re, agrees⟩

/-- Membership in a computed list is computable. -/
theorem member_computable {γ δ : Type} [Primcodable γ] [Primcodable δ] [DecidableEq δ]
    {list : γ → List δ} {item : γ → δ} (listed : Computable list) (picked : Computable item) :
    Computable fun a => decide (item a ∈ list a) := by
  have index : Computable fun a => (list a).idxOf (item a) :=
    Primrec.list_idxOf.to_comp.comp picked listed
  refine (Primrec.nat_lt.decide.to_comp.comp index (Computable.list_length.comp listed)).of_eq fun a => ?_
  simp [List.idxOf_lt_length_iff]

/-- **Bounded listings enumerate**: when a function computable on codes lists, for a bound and a first argument,
finitely many second arguments, every related second argument at some bound, and distinct second arguments have
distinct codes, the relation is enumerable on codes. -/
theorem enumerableOnCodes_of_bounded {R : α → β → Prop} {listing : ℕ → α → List β}
    (injective : Function.Injective (code : β → ℕ)) (computable : CodeComputable₂ listing)
    (exact : ∀ a b, R a b ↔ ∃ bound, b ∈ listing bound a) : EnumerableOnCodes R := by
  obtain ⟨track, trackComputable, tracks⟩ := computable
  have decoded : ∀ bound a, Denumerable.ofNat (List ℕ) (track (Nat.pair bound (code a))) =
      (listing bound a).map code := fun bound a => by
    have tracked := tracks (bound, a)
    simp only [code_pair, code_nat] at tracked
    rw [tracked, ofNat_code_list]
  have test : Computable fun x : (ℕ × ℕ) × ℕ =>
      decide (x.1.2 ∈ Denumerable.ofNat (List ℕ) (track (Nat.pair x.2 x.1.1))) :=
    member_computable ((Primrec.ofNat (List ℕ)).to_comp.comp (trackComputable.comp
      (Primrec₂.natPair.to_comp.comp Computable.snd (Computable.fst.comp Computable.fst))))
      (Computable.snd.comp Computable.fst)
  have search : Partrec fun p : ℕ × ℕ => Nat.rfind fun bound =>
      (decide (p.2 ∈ Denumerable.ofNat (List ℕ) (track (Nat.pair bound p.1))) : Part Bool) :=
    Partrec.rfind test.partrec
  refine ⟨fun p => ∃ bound, p.2 ∈ Denumerable.ofNat (List ℕ) (track (Nat.pair bound p.1)),
    (Partrec.dom_re search).of_eq fun p => Nat.rfind_dom.trans ?_, fun a b => ?_⟩
  · simp
  · rw [exact]
    simp only [decoded]
    constructor
    · rintro ⟨bound, member⟩
      obtain ⟨found, inside, same⟩ := List.mem_map.mp member
      exact ⟨bound, injective same ▸ inside⟩
    · rintro ⟨bound, inside⟩
      exact ⟨bound, List.mem_map_of_mem inside⟩

end Relations

/-! ## Mathlib's encodings -/

section Mathlib

variable {γ δ : Type} [Primcodable γ] [Primcodable δ] [Coded γ] [Coded δ]

/-- Decoding a pair of numbers into a pair of values. -/
def decodePair (p : ℕ × ℕ) : Option (γ × δ) :=
  (Encodable.decode p.1 : Option γ).bind fun a => (Encodable.decode p.2 : Option δ).map fun b => (a, b)

omit [Coded γ] [Coded δ] in
theorem decodePair_computable : Computable (decodePair (γ := γ) (δ := δ)) :=
  Computable.option_bind (Computable.decode.comp Computable.fst)
    (Computable.option_map (Computable.decode.comp (Computable.snd.comp Computable.fst))
      (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd).to₂).to₂

omit [Coded γ] [Coded δ] in
theorem decodePair_encode (a : γ) (b : δ) :
    decodePair (Encodable.encode a, Encodable.encode b) = some (a, b) := by
  simp [decodePair, Encodable.encodek]

/-- **Decidable on codes is Mathlib's computable predicate** at Mathlib's encodings. -/
theorem decidableOnCodes_iff (codeLeft : ∀ a : γ, code a = Encodable.encode a)
    (codeRight : ∀ b : δ, code b = Encodable.encode b) (R : γ → δ → Prop) :
    DecidableOnCodes R ↔ ComputablePred fun p : γ × δ => R p.1 p.2 := by
  constructor
  · rintro ⟨test, computable, agrees⟩
    refine ComputablePred.computable_iff.mpr ⟨fun p => test (Encodable.encode p.1, Encodable.encode p.2),
      computable.comp ((Computable.encode.comp Computable.fst).pair (Computable.encode.comp Computable.snd)), ?_⟩
    funext p
    beta_reduce
    rw [← codeLeft, ← codeRight]
    exact propext (agrees p.1 p.2).symm
  · intro decidable
    obtain ⟨test, computable, same⟩ := ComputablePred.computable_iff.mp decidable
    refine ⟨fun p => ((decodePair p).map test).getD false,
      Computable.option_getD (Computable.option_map decodePair_computable (computable.comp Computable.snd).to₂)
        (Computable.const false), fun a b => ?_⟩
    have here := congrFun same (a, b)
    simp only at here
    rw [codeLeft, codeRight]
    beta_reduce
    rw [decodePair_encode, here]
    rfl

omit [Primcodable γ] [Primcodable δ] [Coded γ] [Coded δ] in
private theorem assert_unit_dom (P : Prop) : (Part.assert P fun _ => Part.some ()).Dom ↔ P := by
  by_cases held : P
  · rw [Part.assert_pos held]; simp [held]
  · rw [Part.assert_neg held]; simp [held]

/-- **Enumerable on codes is Mathlib's recursively enumerable predicate** at Mathlib's encodings. -/
theorem enumerableOnCodes_iff (codeLeft : ∀ a : γ, code a = Encodable.encode a)
    (codeRight : ∀ b : δ, code b = Encodable.encode b) (R : γ → δ → Prop) :
    EnumerableOnCodes R ↔ REPred fun p : γ × δ => R p.1 p.2 := by
  constructor
  · rintro ⟨listed, enumerable, agrees⟩
    have composed : REPred fun p : γ × δ => listed (Encodable.encode p.1, Encodable.encode p.2) :=
      Partrec.comp enumerable ((Computable.encode.comp Computable.fst).pair (Computable.encode.comp Computable.snd))
    refine composed.of_eq fun p => ?_
    rw [← codeLeft, ← codeRight]
    exact agrees p.1 p.2
  · intro enumerable
    have bound : Partrec fun p : ℕ × ℕ => ((decodePair p : Option (γ × δ)) : Part (γ × δ)).bind
        fun x => Part.assert (R x.1 x.2) fun _ => Part.some () :=
      Partrec.bind (Computable.ofOption decodePair_computable) (Partrec.comp enumerable Computable.snd)
    refine ⟨fun p => ∃ x, decodePair p = some x ∧ R x.1 x.2, (Partrec.dom_re bound).of_eq fun p => ?_,
      fun a b => ?_⟩
    · cases found : (decodePair p : Option (γ × δ)) with
      | none => simp
      | some x => simp [assert_unit_dom]
    · rw [codeLeft, codeRight]
      beta_reduce
      rw [decodePair_encode]
      simp

theorem code_list_of_encode (agree : ∀ a : γ, code a = Encodable.encode a) :
    ∀ members : List γ, code members = Encodable.encode members
  | [] => rfl
  | first :: rest => by
      have later := code_list_of_encode agree rest
      rw [code_list] at later ⊢
      rw [List.map_cons, Encodable.encode_list_cons, Encodable.encode_list_cons, later, agree]
      rfl

/-- **Computable on codes is computable** at Mathlib's encodings. -/
theorem CodeComputable.computable {f : γ → δ} (codeLeft : ∀ a : γ, code a = Encodable.encode a)
    (codeRight : ∀ b : δ, code b = Encodable.encode b) (computable : CodeComputable f) : Computable f := by
  obtain ⟨track, trackComputable, tracks⟩ := computable
  exact Computable.encode_iff.mp ((trackComputable.comp Computable.encode).of_eq fun a => by
    rw [← codeLeft, tracks, codeRight])

end Mathlib

end Mettapedia.Computability

#print axioms Mettapedia.Computability.enumerableOnCodes_of_bounded
#print axioms Mettapedia.Computability.decidableOnCodes_iff
#print axioms Mettapedia.Computability.enumerableOnCodes_iff
#print axioms Mettapedia.Computability.CodeComputable.computable
