import Data.Nat

%default total

p : a -> Type
q : a -> Type

    -- ∀ x ∈ X. P(x)  -- f : (x : Type) -> P(x)
    -- ∃ x ∈ X. P(x)  -- ( x : Type ** P(x) ) -- DPair
    -- ∀ a b : Nat. ∃ m : Nat. (m = a /\ m >= b) \/ (m = b /\ m >= a)

f1 : (x : a) -> (p x -> p x)
f1 x y = y

f2 : (x : a ** (p x, q x)) -> (((y : a ** p y)), (z : a ** p z))
f2 ((fs ** sn)) = ((fs ** fst sn), (fs ** fst sn))

f3 : (x : Nat ** ((y : Nat) -> LTE x y))
f3 = (0 ** \y => LTEZero)

lol : (n : Nat) -> LTE n n
lol 0 = LTEZero
lol (S k) = LTESucc (lol k)

f4 : (n : Nat) -> (m : Nat ** LTE n m)
f4 n = (n ** lol n)

lol' : (x : Nat) -> LTE x (S x)
lol' 0 = LTEZero
lol' (S k) = LTESucc (lol' k)

f4' : (n : Nat) -> (m : Nat ** LTE n m)
f4' n = (S n ** lol' n)
