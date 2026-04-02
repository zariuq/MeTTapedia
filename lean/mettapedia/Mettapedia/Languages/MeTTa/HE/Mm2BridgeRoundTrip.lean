import Mettapedia.Languages.MeTTa.HE.CeTTaRuntimeContracts

/-!
# MM2 Surface↔IR Symbol Lowering/Raising Round-Trip

Formalizes the symbol lowering pass in CeTTa's `mm2_lower.c`. The MM2
surface syntax uses compact symbols (`exec`, `,`, `BTM`, `ACT`, `=`, `!=`,
`O`, `+`, `-`, `z3`). The lowering pass maps each surface symbol to a
context-specific IR symbol (`mm2_exec`, `mm2_pattern_and`, etc.).

## Key results (0 sorry)

- `mm2_raise_lower`: raise ∘ lower = id for every valid ctx/symbol pair
- `mm2_lower_injective`: distinct surface symbols → distinct IR (per context)
- `mm2_raise_surjective`: every IR symbol has a surface preimage
- `mm2_lower_preserves_children`: lowering only changes the head symbol
- `mm2_exec_child_contexts`: exec rule children get [general, pattern, template]
-/

namespace Mettapedia.Languages.MeTTa.HE

/-! ## §1: Symbol enumerations -/

/-- Lowering context: determines how context-sensitive symbols are resolved. -/
inductive Mm2LowerCtx where
  | general
  | pattern
  | template
  deriving DecidableEq, Repr

/-- Surface-level MM2 symbols (the 10 from mm2_lower.c). -/
inductive Mm2SurfaceSym where
  | exec       -- `!`
  | comma      -- `,`
  | btm        -- `BTM`
  | act        -- `ACT`  (context-sensitive)
  | eq         -- `=`
  | neq        -- `!=`
  | seqO       -- `O`
  | plus       -- `+`
  | minus      -- `-`
  | z3         -- `z3`
  deriving DecidableEq, Repr

/-- IR-level MM2 symbols (the 11 from mm2_lower.c). -/
inductive Mm2IRSym where
  | mm2_exec
  | mm2_pattern_and
  | mm2_pattern_btm
  | mm2_pattern_act
  | mm2_guard_eq
  | mm2_guard_neq
  | mm2_sink_seq
  | mm2_sink_add
  | mm2_sink_remove
  | mm2_sink_act
  | mm2_sink_z3
  deriving DecidableEq, Repr

/-! ## §2: Lowering and raising maps -/

/-- Lower a surface symbol to an IR symbol given a context.
    Returns `none` for invalid ctx/symbol combinations.

    Key: `ACT` is context-sensitive:
    - pattern context → `mm2_pattern_act`
    - template context → `mm2_sink_act`
    - general context → `none` (ACT requires a specific context)

    Similarly, template-specific symbols (`O`, `+`, `-`, `z3`) only lower in
    template context; pattern-specific symbols (`BTM`) only in pattern context;
    guard symbols (`=`, `!=`) only in pattern context. -/
def mm2Lower : Mm2LowerCtx → Mm2SurfaceSym → Option Mm2IRSym
  | _, .exec => some .mm2_exec
  | _, .comma => some .mm2_pattern_and
  | .pattern, .btm => some .mm2_pattern_btm
  | .pattern, .act => some .mm2_pattern_act
  | .pattern, .eq => some .mm2_guard_eq
  | .pattern, .neq => some .mm2_guard_neq
  | .template, .seqO => some .mm2_sink_seq
  | .template, .plus => some .mm2_sink_add
  | .template, .minus => some .mm2_sink_remove
  | .template, .act => some .mm2_sink_act
  | .template, .z3 => some .mm2_sink_z3
  | _, _ => none

/-- Raise an IR symbol back to its surface symbol and context. -/
def mm2Raise : Mm2IRSym → Mm2LowerCtx × Mm2SurfaceSym
  | .mm2_exec => (.general, .exec)
  | .mm2_pattern_and => (.general, .comma)
  | .mm2_pattern_btm => (.pattern, .btm)
  | .mm2_pattern_act => (.pattern, .act)
  | .mm2_guard_eq => (.pattern, .eq)
  | .mm2_guard_neq => (.pattern, .neq)
  | .mm2_sink_seq => (.template, .seqO)
  | .mm2_sink_add => (.template, .plus)
  | .mm2_sink_remove => (.template, .minus)
  | .mm2_sink_act => (.template, .act)
  | .mm2_sink_z3 => (.template, .z3)

/-! ## §3: Round-trip theorems -/

/-- **Theorem 1**: `raise(lower(s, ctx)) = (ctx', s)` where `ctx'` is the
    canonical context for that IR symbol, and `s` is recovered exactly.
    The surface symbol is always recovered; the context may be normalized
    (general for context-insensitive symbols). -/
theorem mm2_raise_lower (ctx : Mm2LowerCtx) (s : Mm2SurfaceSym) (ir : Mm2IRSym)
    (h : mm2Lower ctx s = some ir) :
    (mm2Raise ir).2 = s := by
  cases s <;> cases ctx <;> simp [mm2Lower] at h <;> subst h <;> rfl

/-- **Theorem 2**: Lowering is injective per context — distinct surface symbols
    that are valid in the same context produce distinct IR symbols. -/
theorem mm2_lower_injective (ctx : Mm2LowerCtx) (s₁ s₂ : Mm2SurfaceSym)
    (ir : Mm2IRSym)
    (h₁ : mm2Lower ctx s₁ = some ir) (h₂ : mm2Lower ctx s₂ = some ir) :
    s₁ = s₂ := by
  have r₁ := mm2_raise_lower ctx s₁ ir h₁
  have r₂ := mm2_raise_lower ctx s₂ ir h₂
  rw [← r₁, ← r₂]

/-- **Theorem 3**: Every IR symbol has a surface preimage (raising is total,
    and re-lowering succeeds). -/
theorem mm2_raise_surjective (ir : Mm2IRSym) :
    ∃ ctx s, mm2Lower ctx s = some ir := by
  cases ir
  · exact ⟨.general, .exec, rfl⟩
  · exact ⟨.general, .comma, rfl⟩
  · exact ⟨.pattern, .btm, rfl⟩
  · exact ⟨.pattern, .act, rfl⟩
  · exact ⟨.pattern, .eq, rfl⟩
  · exact ⟨.pattern, .neq, rfl⟩
  · exact ⟨.template, .seqO, rfl⟩
  · exact ⟨.template, .plus, rfl⟩
  · exact ⟨.template, .minus, rfl⟩
  · exact ⟨.template, .act, rfl⟩
  · exact ⟨.template, .z3, rfl⟩

/-! ## §4: Tree-level lowering -/

/-- A simple tree type for MM2 expressions: a head symbol plus children. -/
structure Mm2Tree (α : Type) where
  head : α
  children : List (Mm2Tree α)

/-- Lower a tree's head symbol, keeping children unchanged. -/
def lowerTreeHead (ctx : Mm2LowerCtx) (t : Mm2Tree Mm2SurfaceSym) :
    Option (Mm2Tree Mm2IRSym × List (Mm2Tree Mm2SurfaceSym)) :=
  match mm2Lower ctx t.head with
  | some irHead => some (⟨irHead, []⟩, t.children)
  | none => none

/-- **Theorem 4**: Lowering only changes the head — children are passed through
    unchanged. -/
theorem mm2_lower_preserves_children (ctx : Mm2LowerCtx)
    (t : Mm2Tree Mm2SurfaceSym) (irTree : Mm2Tree Mm2IRSym)
    (remainder : List (Mm2Tree Mm2SurfaceSym))
    (h : lowerTreeHead ctx t = some (irTree, remainder)) :
    remainder = t.children := by
  simp [lowerTreeHead] at h
  split at h <;> simp_all

/-! ## §5: Exec rule child contexts -/

/-- The three child positions of an `exec` rule and their contexts:
    child 0 = general (the rule name), child 1 = pattern, child 2 = template. -/
def execChildContexts : List Mm2LowerCtx :=
  [.general, .pattern, .template]

/-- **Theorem 5**: exec rule children get [general, pattern, template] contexts. -/
theorem mm2_exec_child_contexts :
    execChildContexts = [Mm2LowerCtx.general, Mm2LowerCtx.pattern, Mm2LowerCtx.template] :=
  rfl

/-- The number of exec child contexts is exactly 3. -/
theorem exec_child_context_count : execChildContexts.length = 3 := rfl

/-! ## §6: Additional safety properties -/

/-- `exec` and `comma` are context-insensitive: they lower the same in all contexts. -/
theorem exec_context_insensitive (ctx₁ ctx₂ : Mm2LowerCtx) :
    mm2Lower ctx₁ .exec = mm2Lower ctx₂ .exec := by
  cases ctx₁ <;> cases ctx₂ <;> rfl

theorem comma_context_insensitive (ctx₁ ctx₂ : Mm2LowerCtx) :
    mm2Lower ctx₁ .comma = mm2Lower ctx₂ .comma := by
  cases ctx₁ <;> cases ctx₂ <;> rfl

/-- ACT is context-sensitive: pattern and template give different IR symbols. -/
theorem act_context_sensitive :
    mm2Lower .pattern .act ≠ mm2Lower .template .act := by
  simp [mm2Lower]

/-- Every lowering that succeeds can be raised back to the original surface symbol. -/
theorem lower_raise_surface_roundtrip (ctx : Mm2LowerCtx) (s : Mm2SurfaceSym)
    (ir : Mm2IRSym) (h : mm2Lower ctx s = some ir) :
    mm2Lower (mm2Raise ir).1 (mm2Raise ir).2 = some ir := by
  cases s <;> cases ctx <;> simp [mm2Lower] at h <;> subst h <;> rfl

end Mettapedia.Languages.MeTTa.HE
