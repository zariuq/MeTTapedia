namespace PriorityStream
scoped infixl:65 (name := lowAdd) (priority := 900) " %%% " => Nat.add
scoped infixl:65 (name := highAdd) (priority := 1100) " %%% " => Nat.add
#check 1 %%% 2 %%% 3
end PriorityStream
namespace TieStream
scoped infixr:65 (name := firstAdd) " %%! " => Nat.add
scoped infixr:65 (name := secondAdd) " %%! " => Nat.add
#check 1 %%! 2 %%! 3
end TieStream
namespace PrecStream
scoped infixl:50 (name := outerAdd) (priority := 1100) " %%? " => Nat.add
scoped infixl:60 (name := innerAdd) (priority := 900) " %%? " => Nat.add
#check 1 %%? 2 %%? 3
end PrecStream
