import Mettapedia.Languages.Agda.Native.SyntaxCodec

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Native.Codec
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.Languages.Agda.Structural
open Statics

def typeParameter (n : Nat) : Codec (TypeParameter n) :=
  (Codec.nat.prod (rawTerm n .term)).ofEquiv
    { toFun := fun A => (A.level, A.term), invFun := fun p => ⟨p.1, p.2⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }

def putTermBody {n : Nat} : TermBody n → Data
  | .bind body => .pair (.atom 0) ((rawTerm (n + 1) .term).put body)
  | .noBind body => .pair (.atom 1) ((rawTerm n .term).put body)

def getTermBody (n : Nat) : Data → Option (TermBody n)
  | .pair (.atom 0) body => (rawTerm (n + 1) .term).get body |>.map TermBody.bind
  | .pair (.atom 1) body => (rawTerm n .term).get body |>.map TermBody.noBind
  | _ => none

def termBody (n : Nat) : Codec (TermBody n) where
  put := putTermBody
  get := getTermBody n
  get_put body := by cases body <;> simp only [putTermBody, getTermBody, Codec.get_put] <;> rfl

def putTypeBody {n : Nat} : TypeBody n → Data
  | .bind body => .pair (.atom 0) ((typeParameter (n + 1)).put body)
  | .noBind body => .pair (.atom 1) ((typeParameter n).put body)

def getTypeBody (n : Nat) : Data → Option (TypeBody n)
  | .pair (.atom 0) body => (typeParameter (n + 1)).get body |>.map TypeBody.bind
  | .pair (.atom 1) body => (typeParameter n).get body |>.map TypeBody.noBind
  | _ => none

def typeBody (n : Nat) : Codec (TypeBody n) where
  put := putTypeBody
  get := getTypeBody n
  get_put body := by cases body <;> simp only [putTypeBody, getTypeBody, Codec.get_put] <;> rfl

end Mettapedia.Languages.Agda.Native.Codec
