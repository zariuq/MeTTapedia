import Std

/-!
# Dependency-directed recompilation

The generic incremental invariant separates source semantics from dependency
bookkeeping. A compiler states which keys it reads. Refreshing precisely the
sources whose keys changed restores the same code as recompiling everything.
This theorem does not assume that an unverified emitter tracks every dependency.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.Refresh

variable {Key Datum Source Code : Type}

structure Compiler (Key Datum Source Code : Type) where
  dependencies : Source → List Key
  compile : (Key → Datum) → Source → Code
  respects : ∀ before after source,
    (∀ key ∈ dependencies source, before key = after key) →
      compile before source = compile after source

def affected (compiler : Compiler Key Datum Source Code) (changed : Key → Bool)
    (source : Source) : Bool :=
  (compiler.dependencies source).any changed

def update (compiler : Compiler Key Datum Source Code) (changed : Key → Bool)
    (after : Key → Datum) (old : Source → Code) (source : Source) : Code :=
  if affected compiler changed source then compiler.compile after source else old source

theorem unchanged_source_keeps_code (compiler : Compiler Key Datum Source Code)
    (changed : Key → Bool) (after : Key → Datum) (old : Source → Code) (source : Source)
    (h : affected compiler changed source = false) :
    update compiler changed after old source = old source := by
  simp [update, h]

theorem update_eq_fresh_compile (compiler : Compiler Key Datum Source Code)
    (before after : Key → Datum) (old : Source → Code)
    (valid : ∀ source, old source = compiler.compile before source)
    (changed : Key → Bool)
    (covers : ∀ key, changed key = false → before key = after key) (source : Source) :
    update compiler changed after old source = compiler.compile after source := by
  by_cases h : affected compiler changed source = true
  · simp [update, h]
  · have same : ∀ key ∈ compiler.dependencies source, before key = after key := by
      intro key hk
      apply covers key
      cases hc : changed key with
      | false => rfl
      | true => exact False.elim (h (List.any_eq_true.2 ⟨key, hk, hc⟩))
    simp [update, h, valid source, compiler.respects before after source same]

/-- Refresh composes across any finite edit sequence by preserving its invariant
after each update, including declaration keys as well as equation keys. -/
theorem update_preserves_invariant (compiler : Compiler Key Datum Source Code)
    (before after : Key → Datum) (old : Source → Code)
    (valid : old = compiler.compile before) (changed : Key → Bool)
    (covers : ∀ key, changed key = false → before key = after key) :
    update compiler changed after old = compiler.compile after := by
  funext source
  exact update_eq_fresh_compile compiler before after old
    (fun source => congrFun valid source) changed covers source

end Mettapedia.Logic.ConstraintTypes.Refresh
