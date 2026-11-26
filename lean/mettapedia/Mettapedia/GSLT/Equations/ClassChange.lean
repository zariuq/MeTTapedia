import Mettapedia.GSLT.Equations.RecipeMatching

/-! # Relabelling, merging, and repairing constructor recipes

Changing an identifier is not necessarily changing an equation. An
injective renaming transports answers both ways. A class merge only gives
forward transport, and may bring two recipes into conflict at their new
argument key. The exact functional-dependency test identifies this
additional work before a graph may be used as a reconciled catalogue.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.ClassChange

open UniversalAlgebra RecipeMatching

variable {S : Signature} {C D : Type*}

def relabel (f : C → D) (before : Catalogue S C) : Catalogue S D where
  rows h := (before.rows h).map fun (result, args) => (f result, f ∘ args)

theorem match_forward (f : C → D) (g : Catalogue S C) (ρ : Nat → C) (p : Term S) (c : C) :
    g.Matches ρ p c → (relabel f g).Matches (f ∘ ρ) p (f c) := by
  induction p generalizing c with
  | var v => exact congrArg f
  | op h ps ih =>
    rintro ⟨args, present, children⟩
    refine ⟨f ∘ args, ?_, fun i => ih i _ (children i)⟩
    exact List.mem_map.mpr ⟨(c, args), present, rfl⟩

theorem match_iff_of_injective (f : C → D) (inj : Function.Injective f)
    (g : Catalogue S C) (ρ : Nat → C) (p : Term S) (c : C) :
    (relabel f g).Matches (f ∘ ρ) p (f c) ↔ g.Matches ρ p c := by
  refine ⟨?_, match_forward f g _ _ _⟩
  induction p generalizing c with
  | var v => exact fun e => inj e
  | op h ps ih =>
    rintro ⟨keys, present, children⟩
    obtain ⟨⟨out, args⟩, old, positions⟩ := List.mem_map.mp present
    have eq : out = c := inj (congrArg Prod.fst positions)
    subst out
    have inputs : f ∘ args = keys := congrArg Prod.snd positions
    subst keys
    exact ⟨args, old, fun i => ih i _ (children i)⟩

/-- This is the exact parent-collision boundary. Grouping by canonical
argument tuple and operation represents a function precisely when all
the parent classes in each group are reconciled. A class merge need not
satisfy it, even when the original catalogue was already functional. -/
theorem functional_after_iff (f : C → D) (g : Catalogue S C) :
    (relabel f g).Functional ↔
      ∀ h a b xs ys, (a, xs) ∈ g.rows h → (b, ys) ∈ g.rows h →
        (∀ i, f (xs i) = f (ys i)) → f a = f b := by
  constructor
  · intro good h a b xs ys ha hb eq
    have first : (f a, f ∘ xs) ∈ (relabel f g).rows h :=
      List.mem_map.mpr ⟨(a, xs), ha, rfl⟩
    have second : (f b, f ∘ ys) ∈ (relabel f g).rows h :=
      List.mem_map.mpr ⟨(b, ys), hb, rfl⟩
    have tuple : f ∘ xs = f ∘ ys := funext eq
    exact good h (f ∘ ys) (f a) (f b) (tuple ▸ first) second
  · intro reconciled h keys a b ha hb
    obtain ⟨⟨lhs, xs⟩, ha, eqA⟩ := List.mem_map.mp ha
    obtain ⟨⟨rhs, ys⟩, hb, eqB⟩ := List.mem_map.mp hb
    have args : f ∘ xs = f ∘ ys := (congrArg Prod.snd eqA).trans (congrArg Prod.snd eqB).symm
    exact (congrArg Prod.fst eqA).symm.trans
      ((reconciled h lhs rhs xs ys ha hb (congrFun args)).trans (congrArg Prod.fst eqB))

end Mettapedia.GSLT.Equations.ClassChange
