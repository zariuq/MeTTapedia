namespace Mettapedia.Languages.MeTTa.PureKernel.Syntax

/-- Core MeTTa-Pure term syntax, scoped by de Bruijn depth. -/
inductive PureTm : Nat → Type where
  | var : Fin n → PureTm n
  | u0 : PureTm n
  | u1 : PureTm n
  | pi : PureTm n → PureTm (n + 1) → PureTm n
  | sigma : PureTm n → PureTm (n + 1) → PureTm n
  | id : PureTm n → PureTm n → PureTm n → PureTm n
  | lam : PureTm (n + 1) → PureTm n
  | app : PureTm n → PureTm n → PureTm n
  | pair : PureTm n → PureTm n → PureTm n
  | fst : PureTm n → PureTm n
  | snd : PureTm n → PureTm n
  | refl : PureTm n → PureTm n
deriving DecidableEq, Repr

end Mettapedia.Languages.MeTTa.PureKernel.Syntax

