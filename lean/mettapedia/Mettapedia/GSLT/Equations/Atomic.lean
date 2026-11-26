import Mettapedia.GSLT.Contracts.ScopedAliasSections

/-! # The free algebra after atomic identification

Only leaves are identified. Application is still a free binary constructor.
An open pattern has the usual first-order meaning, with one value per
variable, not one independent value per occurrence of a variable.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.Atomic

open Contracts.ScopedAliasSections (GTerm)

variable {S C V : Type*}

/-- Change the alphabet without changing the application tree. -/
def rename (f : S → C) : GTerm S → GTerm C
  | .sym s => .sym (f s)
  | .app l r => .app (rename f l) (rename f r)

theorem rename_eq_iff (f : S → C) (s t : GTerm S) :
    rename f s = rename f t ↔ s.EqMod (fun x y => f x = f y) t := by
  induction s generalizing t with
  | sym s => cases t <;> simp [rename, GTerm.EqMod]
  | app l r il ir =>
    cases t with
    | sym s => simp [rename, GTerm.EqMod]
    | app l' r' => simp [rename, GTerm.EqMod, il, ir]

theorem rename_surjective (f : S → C) (onto : Function.Surjective f) :
    Function.Surjective (rename f) := by
  intro t
  induction t with
  | sym c =>
    obtain ⟨s, rfl⟩ := onto c
    exact ⟨.sym s, rfl⟩
  | app _ _ il ir =>
    obtain ⟨l, rfl⟩ := il
    obtain ⟨r, rfl⟩ := ir
    exact ⟨.app l r, rfl⟩

theorem rename_kernel (e : Setoid S) (s t : GTerm S) :
    rename (Quotient.mk e) s = rename (Quotient.mk e) t ↔ s.EqMod e.r t := by
  rw [rename_eq_iff]
  have kernel : (fun x y => Quotient.mk e x = Quotient.mk e y) = e.r := by
    funext x y
    exact propext Quotient.eq_iff_equiv
  rw [kernel]

/-- Shape-wise atomic equivalence is the *least* application congruence
extending the leaf relation. The converse uses the model on class-labelled
trees, rather than an assumption that application must stay injective. -/
theorem least (e : Setoid S) (r : GTerm S → GTerm S → Prop)
    (leaf : ∀ ⦃a b⦄, e.r a b → r (.sym a) (.sym b))
    (app : ∀ ⦃a b c d⦄, r a b → r c d → r (.app a c) (.app b d))
    (s t : GTerm S) (h : s.EqMod e.r t) : r s t := by
  induction s generalizing t with
  | sym s =>
    cases t with
    | sym t => exact leaf h
    | app _ _ => exact False.elim h
  | app l r' il ir =>
    cases t with
    | sym _ => exact False.elim h
    | app l' r'' => exact app (il l' h.1) (ir r'' h.2)

def equivalence (e : Setoid S) : Setoid (GTerm S) where
  r := GTerm.EqMod e.r
  iseqv := by
    refine ⟨fun t => (rename_kernel e t t).1 rfl, ?_, ?_⟩
    · intro a b h
      exact (rename_kernel e b a).1 ((rename_kernel e a b).2 h).symm
    · intro a b c h h'
      exact (rename_kernel e a c).1
        (((rename_kernel e a b).2 h).trans ((rename_kernel e b c).2 h'))

/-- Quotienting a free applicative algebra by leaf equations gives the
free applicative algebra on the quotient alphabet. -/
noncomputable def freeQuotient (e : Setoid S) :
    Quotient (equivalence e) ≃ GTerm (Quotient e) := by
  let encode : Quotient (equivalence e) → GTerm (Quotient e) :=
    Quotient.lift (rename (Quotient.mk e))
      (fun s t h => (rename_kernel e s t).2 h)
  refine Equiv.ofBijective encode ⟨?_, ?_⟩
  · intro x y same
    induction x using Quotient.inductionOn with
    | _ s =>
      induction y using Quotient.inductionOn with
      | _ t => exact Quotient.sound ((rename_kernel e s t).1 same)
  · intro t
    obtain ⟨s, h⟩ := rename_surjective (Quotient.mk e) Quotient.mk_surjective t
    exact ⟨Quotient.mk (equivalence e) s, h⟩

@[simp] theorem freeQuotient_mk (e : Setoid S) (t : GTerm S) :
    freeQuotient e (Quotient.mk (equivalence e) t) = rename (Quotient.mk e) t :=
  rfl

abbrev Pattern (S V : Type*) := GTerm (S ⊕ V)

def fill (f : S → C) (valuation : V → GTerm C) : Pattern S V → GTerm C
  | .sym (.inl s) => .sym (f s)
  | .sym (.inr v) => valuation v
  | .app l r => .app (fill f valuation l) (fill f valuation r)

theorem rename_fill (f : S → C) (valuation : V → GTerm S) (p : Pattern S V) :
    rename f (fill id valuation p) = fill f (rename f ∘ valuation) p := by
  induction p with
  | sym a => cases a <;> rfl
  | app l r il ir => simp [rename, fill, il, ir]

/-- The literal matcher over any class-key representation, including one
whose keys are not raw members. Repeated variables use the same keyed value. -/
theorem match_iff_keyed (rel : S → S → Prop) (f : S → C)
    (key : ∀ s t, f s = f t ↔ rel s t) (p : Pattern S V)
    (valuation : V → GTerm S) (row : GTerm S) :
    fill f (rename f ∘ valuation) p = rename f row ↔
      (fill id valuation p).EqMod rel row := by
  rw [← rename_fill, rename_eq_iff]
  have kernel : (fun s t => f s = f t) = rel := by
    funext s t
    exact propext (key s t)
  rw [kernel]

theorem open_match_iff (f : S → C) (onto : Function.Surjective f)
    (p : Pattern S V) (row : GTerm S) :
    (∃ σ : V → GTerm S, (fill id σ p).EqMod (fun s t => f s = f t) row) ↔
      ∃ σ : V → GTerm C, fill f σ p = rename f row := by
  constructor
  · rintro ⟨σ, ok⟩
    exact ⟨rename f ∘ σ, (match_iff_keyed _ f (fun _ _ => Iff.rfl) p σ row).2 ok⟩
  · rintro ⟨σ, ok⟩
    let lift := Function.surjInv (rename_surjective f onto)
    have rightInverse := Function.rightInverse_surjInv (rename_surjective f onto)
    have lifts : rename f ∘ (lift ∘ σ) = σ := funext fun v => rightInverse (σ v)
    exact ⟨lift ∘ σ, (match_iff_keyed _ f (fun _ _ => Iff.rfl) p _ row).1
      (lifts.symm ▸ ok)⟩

end Mettapedia.GSLT.Equations.Atomic
