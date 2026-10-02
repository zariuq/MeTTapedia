import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.ChurchLaws

/-!
# The typed component tokens of pairs

For a dependent pair type `csigma A G` with a continuous family:

* a token typed at the domain is the component of a typed first-projection token
  (`Ideal.typedAt_arg0`), and a token typed at the family's value at a finite typed
  part `w` of the domain is the component of a typed second-projection token with
  dependency `w` (`Ideal.typedAt_arg1`);
* **the typed tokens of an element are component tokens** (`Ideal.typed_pair_token`):
  a first-projection token whose component is a token of the first projection, typed
  at the domain part of the type witness; or a second-projection token whose
  dependency is below the first projection and typed at the domain part, and whose
  component is a token of the second projection typed at the family part of the
  witness at the dependency;
* conversely, a token of the first projection of an element typed at the domain is
  the component of a typed token of the element (`Ideal.typed_fst_token`), and a token
  of the second projection of an element of the type, typed at the family's value at
  the first projection, is the component of a typed token of the element whose
  dependency is a finite typed part of the first projection (`Ideal.typed_snd_token`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Domain
namespace Ideal

variable {A : Ideal} {G : Ideal → Ideal}

/-- The family of a dependent pair type carrying its domain is monotone in the
compact argument. -/
theorem csigma_monotone (hG : Cont G) : Monotone fun X => G (projT A (principal X)) :=
  fun h => hG.mono (projT_mono (principal_mono h))

/-- **A typed first-projection token**, from a token typed at the domain. -/
theorem typedAt_arg0 (hG : Cont G) {s : Tok} (hs : TypedAt A s) :
    TypedAt (csigma A G) (.arg .pair 0 [] s) := by
  obtain ⟨a₁, h₁, u₁, t₁⟩ := hs
  exact ⟨Elem.former .sigma a₁ [],
    below_former_elem (csigma_monotone hG) h₁ (fun _ h => absurd h List.not_mem_nil),
    Elem.ty_former (.inr rfl) Elem.isUniv_univ u₁ (fun _ h => absurd h List.not_mem_nil),
    tyTok_fst.2 ⟨List.mem_cons_self, rfl, t₁.mono (Elem.dom_former _ _ _).2⟩⟩

/-- **A typed second-projection token**, from a token typed at the family's value at a
finite typed part of the domain. -/
theorem typedAt_arg1 (hG : Cont G) {w : List Tok} (hw : ∀ r ∈ w, TypedAt A r) {s : Tok}
    (hs : TypedAt (G (projT A (principal w))) s) : TypedAt (csigma A G) (.arg .pair 1 w s) := by
  obtain ⟨a₁, ha₁, hu₁, hty₁⟩ := typedAt_list hw
  obtain ⟨b, hb, hbu, hbs⟩ := hs
  refine ⟨Elem.former .sigma a₁ [(w, b)],
    below_former_elem (csigma_monotone hG) ha₁
      (fun p hp => by rw [List.mem_singleton.1 hp]; exact hb),
    Elem.ty_former (.inr rfl) Elem.isUniv_univ hu₁
      (fun p hp => by rw [List.mem_singleton.1 hp]; exact ⟨hty₁, hbu⟩), ?_⟩
  refine tyTok_snd.2 ⟨List.mem_cons_self, fun c hc => (hty₁ c hc).mono (Elem.dom_former _ _ _).2, ?_⟩
  rw [show fnApp .sigma (Elem.former .sigma a₁ [(w, b)]) w = stepApp [(w, b)] w from
    Elem.fam_former _ _ _ _]
  exact hbs.mono (Le.of_subset fun r hr =>
    mem_stepApp.2 ⟨(w, b), List.mem_singleton_self _, Le.refl _, hr⟩)

/-- **The typed tokens of an element of a dependent pair type are component tokens.** -/
theorem typed_pair_token {x : Ideal} {t : Tok} (ht : x.Mem t) {c : List Tok}
    (hc : Below c (csigma A G)) (hct : TyTok c t) :
    (∃ s, t = .arg .pair 0 [] s ∧ (fst x).Mem s ∧ TyTok (args .sigma 0 c) s) ∨
      ∃ C s, t = .arg .pair 1 C s ∧ Below C (fst x) ∧ (∀ c' ∈ C, TyTok (args .sigma 0 c) c') ∧
        (snd x).Mem s ∧ TyTok (fnApp .sigma c C) s := by
  rcases tyTok_below_sigma hc hct with ⟨s, rfl, hs⟩ | ⟨C, s, rfl, hC, hs⟩
  · exact .inl ⟨s, rfl, subset_closure ht, hs⟩
  · exact .inr ⟨C, s, rfl, fun c' hc' => mem_fst_of_arg1 ht hc', hC, subset_closure ⟨C, ht⟩, hs⟩

/-- **A typed first-projection token of an element**, from a token of its first
projection typed at the domain. -/
theorem typed_fst_token (hG : Cont G) {x : Ideal} {s : Tok} (hs : (fst x).Mem s)
    (hsT : TypedAt A s) : x.Mem (.arg .pair 0 [] s) ∧ TypedAt (csigma A G) (.arg .pair 0 [] s) :=
  ⟨mem_arg0_of_mem_fst hs, typedAt_arg0 hG hsT⟩

/-- **A typed second-projection token of an element of a dependent pair type**, from a
token of its second projection typed at the family's value at its first projection:
the dependency is a finite typed part of the first projection. -/
theorem typed_snd_token (hG : Cont G) {x : Ideal} (hx : projT (csigma A G) x = x) {s : Tok}
    (hs : (snd x).Mem s) (hsT : TypedAt (G (fst x)) s) :
    ∃ w, x.Mem (.arg .pair 1 w s) ∧ TypedAt (csigma A G) (.arg .pair 1 w s) := by
  obtain ⟨b, hb, hbu, hbs⟩ := hsT
  have hfst : projT A (fst x) = fst x := semTyped_fst hG hx
  -- the witness is below the family at a finite part of the first projection
  have hb' : Below b (fam .sigma (former .sigma A fun X => G (projT A (principal X))) (fst x)) := by
    change Below b (fam .sigma (csigma A G) (fst x))
    rw [fam_csigma hG, hfst]
    exact hb
  obtain ⟨Z, hZ, hbZ⟩ := below_fam_former (csigma_monotone hG) hb'
  have hZ' : Below Z (projT A (fst x)) := by
    rw [hfst]
    exact hZ
  obtain ⟨w, hw, hZw⟩ := below_closure_iff.1 hZ'
  exact ⟨w, mem_arg1_of_mem_snd (fun r hr => (hw r hr).1) hs,
    typedAt_arg1 hG (fun r hr => (hw r hr).2)
      ⟨b, fun r hr => csigma_monotone hG hZw r (hbZ r hr), hbu, hbs⟩⟩

end Ideal
end Domain
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
