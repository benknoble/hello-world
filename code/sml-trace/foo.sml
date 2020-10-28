structure Foo = struct
  fun g x = x * x
  fun f x = g (x + 1)
  fun foo x = (f x; f x; f x)
  fun h x y = x + y
end
