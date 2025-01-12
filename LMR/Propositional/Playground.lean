class Foo (α : Type) where
  foo : Nat

instance : Foo String where
  foo := 0

-- `Foo` の deriving handler は作っていないが、String と bar は同じなので
-- String のインスタンスが使用される
def bar := String deriving Foo

-- String のインスタンスが使われている
#guard Foo.foo bar = 0
