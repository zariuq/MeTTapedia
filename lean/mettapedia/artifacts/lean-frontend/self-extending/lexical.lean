namespace LexicalStream
scoped syntax:80 (name := split) " %% " " > " term:81 : term
#check %%> 1
scoped syntax:80 (name := joined) " %%> " term:81 : term
#check %%> 1
#check shimmer
scoped syntax:80 (name := keyword) " shimmer " term:81 : term
#check shimmer 1
end LexicalStream
