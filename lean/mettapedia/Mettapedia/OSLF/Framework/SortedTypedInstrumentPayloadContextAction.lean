import Mettapedia.OSLF.Framework.SortedTypedInstrumentPayloadIPOSystem

/-!
# Complete substitution of heterogeneous encoded context labels

The retained label domain is the image of actual typed context classes.
Composition substitutes their complete sorted siblings and AC1 residues,
then re-encodes the whole context. Both decoder roundtrips, identity and
associativity, and its action on arbitrary native values are earned.

These categorical substitution equations do not assert preservation of
arbitrary payload bisimilarity by an ambient native context.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments.PayloadLabels

open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RedexRelativeCongruence

universe u v
variable {profile : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : profile.Srt → Prop}

theorem encode_readContext {source target : Srt profile Parallel} (label : Label profile Parallel source target) :
    encodeContext (readContext label) = encodeMixed (readLabel label) := by
  change encodeMixed ((contextEquiv (signature := signature profile Parallel) (Parallel := NativeParallel (source := profile) (Parallel := Parallel))
    source target) ((contextEquiv (signature := signature profile Parallel) (Parallel := NativeParallel (source := profile) (Parallel := Parallel))
      source target).symm (readLabel label))) = _
  rw [Equiv.apply_symm_apply]

def EncodedLabel (source target : Srt profile Parallel) :=
  {label : Label profile Parallel source target //
    ∃ context : ContextClass (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel)) source target,
      encodeContext context = label}

def encoded {source target : Srt profile Parallel}
    (context : ContextClass (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel)) source target) :
    EncodedLabel (profile := profile) (Parallel := Parallel) source target := ⟨encodeContext context, context, rfl⟩

def encodedContextEquiv (source target : Srt profile Parallel) :
    EncodedLabel (profile := profile) (Parallel := Parallel) source target ≃
      ContextClass (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel)) source target where
  toFun := fun label => readContext label.val
  invFun := encoded
  left_inv label := by
    apply Subtype.ext
    obtain ⟨context, same⟩ := label.property
    change encodeContext (readContext label.val) = label.val
    rw [← same, read_encodeContext]
  right_inv := read_encodeContext

theorem encoded_fixed_point {source target : Srt profile Parallel}
    (label : EncodedLabel (profile := profile) (Parallel := Parallel) source target) :
    encodeContext (readContext label.val) = label.val :=
  congrArg Subtype.val ((encodedContextEquiv source target).left_inv label)

def substituteLabel {source middle target : Srt profile Parallel}
    (inner : Label profile Parallel source middle) (outer : Label profile Parallel middle target) :
    EncodedLabel (profile := profile) (Parallel := Parallel) source target :=
  encoded ((readContext inner).comp (readContext outer))

theorem substituteLabel_context {source middle target : Srt profile Parallel}
    (inner : Label profile Parallel source middle) (outer : Label profile Parallel middle target) :
    readContext (substituteLabel inner outer).val =
      (readContext inner).comp (readContext outer) :=
  read_encodeContext _

theorem substituteLabel_encoded {source middle target : Srt profile Parallel}
    (inner : ContextClass (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel)) source middle)
    (outer : ContextClass (signature profile Parallel) (NativeParallel (source := profile) (Parallel := Parallel)) middle target) :
    substituteLabel (encodeContext inner) (encodeContext outer) = encoded (inner.comp outer) := by
  simp only [substituteLabel, read_encodeContext]

theorem substituteLabel_assoc {first second third fourth : Srt profile Parallel}
    (inner : Label profile Parallel first second) (middle : Label profile Parallel second third)
    (outer : Label profile Parallel third fourth) :
    substituteLabel (substituteLabel inner middle).val outer =
    substituteLabel inner (substituteLabel middle outer).val := by
  unfold substituteLabel
  change encoded ((readContext (encodeContext ((readContext inner).comp
      (readContext middle)))).comp (readContext outer)) =
    encoded ((readContext inner).comp (readContext (encodeContext
      ((readContext middle).comp (readContext outer)))))
  rw [read_encodeContext, read_encodeContext, ContextClass.comp_assoc]

theorem substituteLabel_left_identity {source target : Srt profile Parallel}
    (label : EncodedLabel (profile := profile) (Parallel := Parallel) source target) :
    substituteLabel (encodeContext (ContextClass.identity
      (signature := signature profile Parallel) (Parallel := NativeParallel (source := profile) (Parallel := Parallel)) source)) label.val = label := by
  apply Subtype.ext
  change encodeContext ((readContext (encodeContext (ContextClass.identity
    (signature := signature profile Parallel) (Parallel := NativeParallel (source := profile) (Parallel := Parallel)) source))).comp
    (readContext label.val)) = label.val
  rw [read_encodeContext, ContextClass.identity_comp, encoded_fixed_point]

theorem substituteLabel_right_identity {source target : Srt profile Parallel}
    (label : EncodedLabel (profile := profile) (Parallel := Parallel) source target) :
    substituteLabel label.val (encodeContext (ContextClass.identity
      (signature := signature profile Parallel) (Parallel := NativeParallel (source := profile) (Parallel := Parallel)) target)) = label := by
  apply Subtype.ext
  change encodeContext ((readContext label.val).comp
    (readContext (encodeContext (ContextClass.identity
      (signature := signature profile Parallel) (Parallel := NativeParallel (source := profile) (Parallel := Parallel)) target)))) = label.val
  rw [read_encodeContext, ContextClass.comp_identity, encoded_fixed_point]

theorem substituteLabel_complete_value {source middle target : Srt profile Parallel}
    (inner : Label profile Parallel source middle) (outer : Label profile Parallel middle target)
    (supplied : ValueClass (source := profile) (Parallel := Parallel) source) :
    (readContext (substituteLabel inner outer).val).fill supplied =
      (readContext outer).fill ((readContext inner).fill supplied) := by
  rw [substituteLabel_context, ContextClass.fill_comp]

theorem actual_step_iff_encoded {source target : Srt profile Parallel}
    (family : ReactionRule (.origin : ContextCategory profile Parallel) → Prop)
    (label : EncodedLabel (profile := profile) (Parallel := Parallel) source target)
    (first : ValueClass (source := profile) (Parallel := Parallel) source) (last : ValueClass (source := profile) (Parallel := Parallel) target) :
    (firingSystem family).act label.val first last ↔
      ActIPO family (RawArrow.context (readContext label.val))
        (RawArrow.value first) (RawArrow.value last) := by
  rw [act_read_iff]
  exact and_iff_right (encoded_fixed_point label)

end Mettapedia.OSLF.Framework.SortedTypedInstruments.PayloadLabels
