namespace ConsumingFailure
scoped syntax:80 (name := short) " %%! " term:81 : term
scoped syntax:80 (name := long) " %%! " term:81 " tail " term:81 : term
#check %%! 1 tail
