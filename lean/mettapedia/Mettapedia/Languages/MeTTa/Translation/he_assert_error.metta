; A literal error compares with itself; the assertion must return the same error.
!(assertEqual (Error (assert False) (False not True))
              (Error (assert False) (False not True)))
!(assertEqual (assert False) (Error (assert False) (False not True)))
