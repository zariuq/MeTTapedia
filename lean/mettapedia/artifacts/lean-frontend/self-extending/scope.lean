namespace StreamScopes
scoped infixl:65 (name := scopedAdd) " %%% " => Nat.add
#check 1 %%% 2
end StreamScopes
section Local
open scoped StreamScopes
local infixr:70 (name := localAdd) " %%! " => Nat.add
#check 1 %%% 2 %%! 3
end Local
section Restored
open scoped StreamScopes
#check 1 %%% 2
end Restored
