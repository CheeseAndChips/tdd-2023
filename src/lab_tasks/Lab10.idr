%default total

f1 : (p, q) -> Either p q
f1 x = Left (fst x)

f2 : (Either (a, b) c) -> ((Either a c), (Either b c))
f2 (Left x) = (Left (fst x), Left (snd x))
f2 (Right x) = (Right x, Right x)

f2' : ((Either a c), (Either b c)) -> (Either (a, b) c)
f2' ((Left x), (Left y)) = Left (x, y)
f2' ((Left x), (Right y)) = Right y
f2' ((Right x), _) = Right x
f2' ((Right x), _) = Right x

f3 : (p -> r) -> ((q -> r) -> ((Either p q) -> r))
f3 f g (Left x) = f x
f3 f g (Right x) = g x

f4 : p -> ((p -> Void) -> Void)
f4 p = \f => f p

f5 : ((p, q) -> Void) -> (p -> (q -> Void))
f5 f x y = f (x, y)

f6 : (Either p q -> Void) -> ((p -> Void), (q -> Void))
f6 f = (\x => f (Left x), \x => f (Right x))

f6' : ((p -> Void), (q -> Void)) -> (Either p q -> Void)
f6' (f, g) (Left x) = f x
f6' (f, g) (Right x) = g x

data EitherOrBoth a b = Left a | Right b | Both a b

f7 : ((p, q) -> Void) -> (EitherOrBoth (p -> Void) (q -> Void))
f7 f = Left ?aa_0

f7' : Either (p -> Void) (q -> Void) -> ((p, q) -> Void)
f7' (Left f) (x, y) = f x
f7' (Right f) (x, y) = f y

f8 : (p -> q) -> ((q -> Void) -> (p -> Void))
f8 f g x = g (f x)
