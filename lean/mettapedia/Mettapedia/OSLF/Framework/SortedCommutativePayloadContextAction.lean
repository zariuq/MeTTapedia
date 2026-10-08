import Mettapedia.OSLF.Framework.SortedCommutativePayloadIPOSystem

/-!
# Complete context substitution for encoded process-bearing labels

The retained label domain is the image of independently formed context
classes. Context composition substitutes the complete closed siblings and
parallel residues, then re-encodes the actual AC1 context. The decoder earns
both the entire context readout and its action on arbitrary native values.
No preservation of arbitrary payload bisimulation by context substitution
is assumed or inferred from these categorical equations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.PayloadLabels

open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u
variable {Symbols : Type u} {arity : Symbols → Nat}

theorem encode_readContext {source target : Srt arity} (label : Label arity source target) :
    encodeContext (readContext label) = encodeMixed (readLabel label) := by
  change encodeMixed ((contextEquiv (signature := signature arity) (Parallel := Parallel arity)
    source target) ((contextEquiv (signature := signature arity) (Parallel := Parallel arity)
      source target).symm (readLabel label))) = _
  rw [Equiv.apply_symm_apply]

def EncodedLabel (source target : Srt arity) :=
  {label : Label arity source target //
    ∃ context : ContextClass (signature arity) (Parallel arity) source target,
      encodeContext context = label}

def encoded {source target : Srt arity}
    (context : ContextClass (signature arity) (Parallel arity) source target) :
    EncodedLabel (arity := arity) source target := ⟨encodeContext context, context, rfl⟩

def encodedContextEquiv (source target : Srt arity) :
    EncodedLabel (arity := arity) source target ≃
      ContextClass (signature arity) (Parallel arity) source target where
  toFun := fun label => readContext label.val
  invFun := encoded
  left_inv label := by
    apply Subtype.ext
    obtain ⟨context, same⟩ := label.property
    change encodeContext (readContext label.val) = label.val
    rw [← same, read_encodeContext]
  right_inv := read_encodeContext

theorem encoded_fixed_point {source target : Srt arity}
    (label : EncodedLabel (arity := arity) source target) :
    encodeContext (readContext label.val) = label.val :=
  congrArg Subtype.val ((encodedContextEquiv source target).left_inv label)

def substituteLabel {source middle target : Srt arity}
    (inner : Label arity source middle) (outer : Label arity middle target) :
    EncodedLabel (arity := arity) source target :=
  encoded ((readContext inner).comp (readContext outer))

theorem substituteLabel_context {source middle target : Srt arity}
    (inner : Label arity source middle) (outer : Label arity middle target) :
    readContext (substituteLabel inner outer).val =
      (readContext inner).comp (readContext outer) :=
  read_encodeContext _

theorem substituteLabel_encoded {source middle target : Srt arity}
    (inner : ContextClass (signature arity) (Parallel arity) source middle)
    (outer : ContextClass (signature arity) (Parallel arity) middle target) :
    substituteLabel (encodeContext inner) (encodeContext outer) = encoded (inner.comp outer) := by
  simp only [substituteLabel, read_encodeContext]

theorem substituteLabel_assoc {first second third fourth : Srt arity}
    (inner : Label arity first second) (middle : Label arity second third)
    (outer : Label arity third fourth) :
    substituteLabel (substituteLabel inner middle).val outer =
    substituteLabel inner (substituteLabel middle outer).val := by
  unfold substituteLabel
  change encoded ((readContext (encodeContext ((readContext inner).comp
      (readContext middle)))).comp (readContext outer)) =
    encoded ((readContext inner).comp (readContext (encodeContext
      ((readContext middle).comp (readContext outer)))))
  rw [read_encodeContext, read_encodeContext, ContextClass.comp_assoc]

theorem substituteLabel_left_identity {source target : Srt arity}
    (label : EncodedLabel (arity := arity) source target) :
    substituteLabel (encodeContext (ContextClass.identity
      (signature := signature arity) (Parallel := Parallel arity) source)) label.val = label := by
  apply Subtype.ext
  change encodeContext ((readContext (encodeContext (ContextClass.identity
    (signature := signature arity) (Parallel := Parallel arity) source))).comp
    (readContext label.val)) = label.val
  rw [read_encodeContext, ContextClass.identity_comp, encoded_fixed_point]

theorem substituteLabel_right_identity {source target : Srt arity}
    (label : EncodedLabel (arity := arity) source target) :
    substituteLabel label.val (encodeContext (ContextClass.identity
      (signature := signature arity) (Parallel := Parallel arity) target)) = label := by
  apply Subtype.ext
  change encodeContext ((readContext label.val).comp
    (readContext (encodeContext (ContextClass.identity
      (signature := signature arity) (Parallel := Parallel arity) target)))) = label.val
  rw [read_encodeContext, ContextClass.comp_identity, encoded_fixed_point]

theorem substituteLabel_complete_value {source middle target : Srt arity}
    (inner : Label arity source middle) (outer : Label arity middle target)
    (supplied : ValueClass arity source) :
    (readContext (substituteLabel inner outer).val).fill supplied =
      (readContext outer).fill ((readContext inner).fill supplied) := by
  rw [substituteLabel_context, ContextClass.fill_comp]

theorem actual_step_iff_encoded {source target : Srt arity}
    (family : ReactionRule (.origin : ContextCategory arity) → Prop)
    (label : EncodedLabel (arity := arity) source target)
    (first : ValueClass arity source) (last : ValueClass arity target) :
    (firingSystem family).act label.val first last ↔
      ActIPO family (RawArrow.context (readContext label.val))
        (RawArrow.value first) (RawArrow.value last) := by
  rw [act_read_iff]
  exact and_iff_right (encoded_fixed_point label)

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.PayloadLabels
