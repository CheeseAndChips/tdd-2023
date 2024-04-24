module Lesson09

import Data.List
import Data.List.Views
import Data.Nat

%default total

data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> (ListLast (xs ++ [x]))

listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case (listLast xs) of
                          Empty => (NonEmpty [] x)
                          (NonEmpty ys y) => (NonEmpty (x :: ys) y)

-- f : List a -> Int
-- f (xs ++ [x]) = ?f_rhs

describeHelper : (input: List Int) -> (form : (ListLast input)) -> String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x) = "Non empty, last one " ++ show x

describe' : (input: List Int) -> String
describe' input = (describeHelper input ((listLast input)))

describe : (input: List Int) -> String
describe input with (listLast input)
  describe [] | Empty = "Empty"
  describe (xs ++ [x]) | (NonEmpty xs x) = "Non empty, last one " ++ show x

describe'' : (input: List Int) -> String
describe'' input = case (listLast input) of
                        Empty => "Empty"
                        (NonEmpty xs x) => "Non empty, last one " ++ show x

covering
myReverse : List a -> List a
myReverse xs with ((listLast xs))
  myReverse [] | Empty = []
  myReverse (ys ++ [x]) | (NonEmpty ys x) = x :: myReverse ys

-- mergeSort : Ord a => List a -> List a
-- mergeSort [] = []
-- mergeSort [x] = [x]
-- mergeSort (left ++ right) = merge (mergeSort left) (mergeSort right)

data SplitList : List a -> Type where
  SplitNil : SplitList []
  SplitOne : SplitList [x]
  SplitPair : (left : List a) -> (right: List a) -> (SplitList (left ++ right))

splitList : (input : List a) -> (SplitList input)
splitList input = splitList' input input
  where
    splitList' : List a -> (input : List a) -> (SplitList input)
    splitList' _ [] = SplitNil
    splitList' _ [x] = SplitOne {x=x}
    splitList' (_ :: _ :: counter) (item :: items) = case splitList' counter items of
                                                          SplitNil => SplitOne
                                                          SplitOne {x} => SplitPair [item] [x]
                                                          (SplitPair left right) => SplitPair (item :: left) right
    splitList' _ items = (SplitPair [] items)

covering
mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (left ++ right) | (SplitPair left right) = merge (mergeSort left) (mergeSort right)

data MySnocList : List a -> Type where
  MyEmpty : MySnocList []
  MySnoc : (x ,xs : _) -> (rec : MySnocList xs) -> MySnocList (xs ++ [x])

snocListHelper : {input : _} -> (snoc : MySnocList input) -> (rest : List a) -> MySnocList (input ++ rest)
snocListHelper snoc [] = rewrite appendNilRightNeutral input in snoc
snocListHelper snoc (x :: xs) =
  rewrite appendAssociative input [x] xs in (snocListHelper ((MySnoc x input snoc)) xs)

snocList' : (xs : List a ) -> MySnocList xs
snocList' xs = snocListHelper MyEmpty xs

reverse'' : List a -> List a
reverse'' xs with (snocList' xs)
  reverse'' [] | MyEmpty = []
  reverse'' (ys ++ [x]) | (MySnoc x ys rec) = x :: (reverse'' ys) | rec

mergeSort'' : Ord a => List a -> List a
mergeSort'' input with (splitRec input)
  mergeSort'' [] | SplitRecNil = []
  mergeSort'' [x] | (SplitRecOne x) = [x]
  mergeSort'' (lefts ++ rights) | (SplitRecPair lefts rights lrec rrec)
    = merge (mergeSort'' lefts | lrec) (mergeSort'' rights | rrec)

data TakeN : List a -> Type where
     NoGroup : TakeN xs
     Fewer : TakeN xs
     Exact : (n_xs : List a) -> (rest: _) -> (rec: TakeN rest) -> TakeN (n_xs ++ rest)

takeN' : (n : Nat) -> (n_gab: Nat) -> (xs : List a) -> TakeN xs
takeN' 0 n_gab xs = ?asdasd
takeN' 1 n_gab (x :: xs) = Exact [x] xs (takeN' n_gab n_gab xs)
takeN' (S k) n_gab [] = NoGroup
takeN' (S k) n_gab (x :: xs) = case (takeN' k n_gab xs) of
                          NoGroup => Fewer
                          Fewer => Fewer
                          (Exact n_xs rest rec) => Exact (x :: n_xs) (rest) rec

takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN n xs = takeN' n n xs

myGroupBy : (n : Nat) -> (xs : List a) -> List (List a)
myGroupBy n xs with (takeN n xs)
  myGroupBy n xs | NoGroup = []
  myGroupBy n xs | Fewer = [xs]
  myGroupBy n (n_xs ++ rest) | (Exact n_xs rest rec) = n_xs :: (myGroupBy n rest) | rec







-- data TakeN : List a -> Type where
--      Fewer : TakeN xs
--      Exact : (n_xs : List a) -> (rest: _) -> (rec: TakeN rest) -> TakeN (n_xs ++ rest)

-- takeN' : (n : Nat) -> (n_gab: Nat) -> (xs : List a) -> TakeN xs
-- takeN' 0 n_gab xs = ?asdasd
-- takeN' 1 n_gab (x :: xs) = Exact [x] xs (takeN' n_gab n_gab xs)
-- takeN' (S k) n_gab [] = Fewer
-- takeN' (S k) n_gab (x :: xs) = case (takeN' k n_gab xs) of
--                           Fewer => Fewer
--                           (Exact n_xs rest rec) => Exact (x :: n_xs) (rest) rec

-- takeN : (n : Nat) -> (xs : List a) -> TakeN xs
-- takeN n xs = takeN' n n xs

-- myGroupBy : (n : Nat) -> (xs : List a) -> List (List a)
-- myGroupBy n xs with (takeN n xs)
--   myGroupBy n xs | Fewer = [xs]
--   myGroupBy n (n_xs ++ rest) | (Exact n_xs rest rec) = n_xs :: (myGroupBy n rest) | rec














-- data TakeN : List a -> Type where
--   Fewer : TakeN xs
--   Exact : (xs: _) -> (rest : _) -> TakeN (xs ++ rest)

-- takeN : (n : Nat) -> (xs : List a) -> TakeN xs
-- takeN 0 xs = Exact [] xs
-- takeN (S k) [] = Fewer
-- takeN (S k) (x :: xs) = case (takeN k xs) of
--                           Fewer => Fewer
--                           (Exact n_xs rest) => Exact (x :: n_xs) rest

-- data TakeGroups : List a -> Type where
--   Last : (xs: _) -> TakeGroups xs
--   NotLast : (xs: _) -> (rest: _) -> (rec: TakeGroups rest) -> TakeGroups (xs ++ rest)



-- takeN : (n : Nat) -> (xs : List a) -> TakeN xs
-- takeN 0 xs = Exact [] xs (Fewer)
-- takeN (S k) [] = Fewer
-- takeN (S k) (x :: xs) = case (takeN k xs) of
--                           Fewer => Fewer
--                           (Exact n_xs rest rec) => aaa x rec n_xs



-- data TakeGroups : List a -> Type where
--   LastGroup : (xs: _) -> TakeGroups xs
--   NotLastGroup : (grp, remaining: _) -> (rec: TakeGroups remaining) -> TakeGroups ( :: []) (S n)

-- groupByN : (n : Nat) -> (xs : List a) -> List (List a)
-- groupByN n xs with (takeN n xs)
--   groupByN n xs | Fewer = [xs]
--   groupByN n (n_xs ++ rest) | (Exact n_xs rest) = n_xs :: groupByN n rest


-- magija : (x : a) -> (xs : List a) -> (ys : List a) -> x :: (xs ++ ys) = (x :: xs) ++ ys

-- takeN : (n : Nat) -> (xs : List a) -> TakeN xs
-- takeN 0 xs = Exact [] (Fewer) xs
-- takeN (S k) [] = Fewer
-- takeN (S k) (x :: xs) = case (takeN k xs) of
--                             Fewer => Fewer
--                             (Exact ys n_xs rest) => rewrite magija x ys rest in Exact (x :: ys) (Exact (x::ys) ys rest) rest
-- covering
-- groupBy : (n : Nat) -> (xs : List a) -> List (List a)
-- groupBy n xs with (takeN n xs)
--   groupBy n xs | Fewer = [xs]
--   groupBy n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupBy n rest













-- div2 : (n : Nat) -> Nat
-- div2 0 = 0
-- div2 (S 0) = 0
-- div2 (S (S k)) = S (div2 k)

-- halves : List a -> (List a, List a)
-- halves xs = case (takeN (div2 $ length xs) xs) of
--                  Fewer => (xs, [])
--                  (Exact n_xs {rest}) => (n_xs, rest)

-- lol : (n : Nat) -> (xs : List a) -> (List a, List a)
-- lol n xs = case takeN n xs of
--                 Fewer => (xs, [])
--                 (Exact n_xs {rest}) => (n_xs, rest)
