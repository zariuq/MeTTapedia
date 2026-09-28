import Mettapedia.OSLF.Syntax.BindingTelescopeSubstitution
import Mettapedia.GSLT.Core.ContextualLadderTerminal
import Mettapedia.GSLT.Core.ContextualComprehension

/-!
# The raw telescope category with families

Contexts retain their complete raw telescope. Types are scoped type codes,
and terms are raw syntax tagged with a proposed type. The tag is bookkeeping,
not a typing certificate. Substitution and comprehension are the actual
binding and telescope operations; the empty telescope is terminal.

This structure is an input to a separate formation and typing admission
construction. It does not assert that arbitrary raw telescopes are formed or
that a tagged raw term inhabits its proposed type in an object-language theory.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.Telescope

open Mettapedia.GSLT.Core.ContextualLadder

abbrev Context (S : Signature) (b k : S.Srt) := Sigma (RawContext S b k)

/-- A proposed type tag with raw term syntax, without typing evidence. -/
structure TaggedTerm {S : Signature} {b k : S.Srt} (context : Context S b k)
    (proposedType : RawTy S b k context.1) where
  code : RawTm S b context.1

variable {S : Signature} {b k : S.Srt}

@[ext] theorem TaggedTerm.ext {context : Context S b k} {A : RawTy S b k context.1}
    {first second : TaggedTerm context A} (same : first.code = second.code) : first = second := by
  cases first
  cases second
  cases same
  rfl

/-- Equality transport changes only the proposed tag. -/
theorem TaggedTerm.cast_code {context : Context S b k} {A B : RawTy S b k context.1}
    (same : A = B) (term : TaggedTerm context A) :
    (cast (congrArg (TaggedTerm context) same) term).code = term.code := by
  cases same
  rfl

def taggedSub {source target : Context S b k} {A : RawTy S b k target.1}
    (term : TaggedTerm target A) (substitution : RawSub S b target.1 source.1) :
    TaggedTerm source (bind substitution A) := ⟨bind substitution term.code⟩

/-- A raw CwF records proposed type tags; formation and typing are additional data. -/
def rawTelescopeCwf (S : Signature) (b k : S.Srt) : Cwf.{0, 0, 0, 0} where
  Ctx := Context S b k
  Sub source target := RawSub S b target.1 source.1
  idS context := identity b context.1
  compS first second := comp first second
  id_comp := comp_identity_left
  comp_id := comp_identity_right
  comp_assoc := comp_assoc
  Ty context := RawTy S b k context.1
  tySub A substitution := bind substitution A
  tySub_id := bind_identity
  tySub_comp A first second := (bind_compose first second A).symm
  Tm context A := TaggedTerm context A
  tmSub := taggedSub
  tmSub_id := by
    intro context A term
    apply TaggedTerm.ext
    change bind (identity b context.1) term.code =
      (cast (congrArg (TaggedTerm context) (bind_identity A).symm) term).code
    exact (bind_identity term.code).trans
      (TaggedTerm.cast_code (bind_identity A).symm term).symm
  tmSub_comp := by
    intro firstContext middleContext lastContext A term first second
    apply TaggedTerm.ext
    change bind (comp first second) term.code =
      (cast (congrArg (TaggedTerm firstContext) (bind_compose first second A))
        (taggedSub (taggedSub term first) second)).code
    exact (bind_compose first second term.code).symm.trans
      (TaggedTerm.cast_code (bind_compose first second A)
        (taggedSub (taggedSub term first) second)).symm
  ext context A := ⟨context.1 + 1, .snoc context.2 A⟩
  wk := fun {context} _ => projection b context.1
  vz := fun {context} _ => ⟨newest b context.1⟩
  pair substitution _ term := pair substitution term.code
  wk_pair substitution _ term := projection_pair substitution term.code
  vz_pair := by
    intro source target substitution A term
    apply TaggedTerm.ext
    change term.code =
      (cast (congrArg (TaggedTerm source)
        (show bind substitution A =
          bind (pair substitution term.code) (bind (projection b target.1) A) from
          ((bind_compose (projection b target.1) (pair substitution term.code) A).trans
            (congrArg (fun sigma => bind sigma A) (projection_pair substitution term.code))).symm))
        term).code
    exact (TaggedTerm.cast_code
      (((bind_compose (projection b target.1) (pair substitution term.code) A).trans
        (congrArg (fun sigma => bind sigma A) (projection_pair substitution term.code))).symm) term).symm
  pair_eta := by
    intro source target A substitution
    change pair (comp (projection b target.1) substitution)
      (cast (congrArg (TaggedTerm source)
        (bind_compose (projection b target.1) substitution A))
        (taggedSub (⟨newest b target.1⟩ :
          TaggedTerm (⟨target.1 + 1, .snoc target.2 A⟩ : Context S b k)
            (bind (projection b target.1) A)) substitution)).code = substitution
    exact (congrArg (pair (comp (projection b target.1) substitution))
      (TaggedTerm.cast_code (bind_compose (projection b target.1) substitution A)
        (taggedSub (⟨newest b target.1⟩ :
          TaggedTerm (⟨target.1 + 1, .snoc target.2 A⟩ : Context S b k)
            (bind (projection b target.1) A)) substitution))).trans
      (pair_projection_newest substitution)

/-- The empty raw telescope is the chosen terminal context. -/
def rawTelescopeCwfWithTerminal (S : Signature) (b k : S.Srt) :
    CwfWithTerminal.{0, 0, 0, 0} where
  toCwf := rawTelescopeCwf S b k
  empty := ⟨0, .nil⟩
  toEmpty context := emptySub b context.1
  toEmpty_unique _ substitution := emptySub_unique substitution

/-- Context comprehension retains the actual declaration, including its code. -/
theorem rawTelescopeCwf_ext (context : Context S b k) (A : RawTy S b k context.1) :
    (rawTelescopeCwf S b k).ext context A = ⟨context.1 + 1, .snoc context.2 A⟩ := rfl

/-- The universal decomposition uses the same underlying projection and newest term. -/
theorem comprehension_components {source target : Context S b k}
    (A : RawTy S b k target.1) (substitution : RawSub S b (target.1 + 1) source.1) :
    let data := (rawTelescopeCwf S b k).decompose A substitution
    (data.1, data.2.code) = split substitution := by
  exact Prod.ext rfl
    (TaggedTerm.cast_code (bind_compose (projection b target.1) substitution A)
      (taggedSub (⟨newest b target.1⟩ :
        TaggedTerm (⟨target.1 + 1, .snoc target.2 A⟩ : Context S b k)
          (bind (projection b target.1) A)) substitution))

#print axioms rawTelescopeCwf
#print axioms rawTelescopeCwfWithTerminal
#print axioms comprehension_components

end Mettapedia.OSLF.Binding.Telescope
