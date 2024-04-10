module Lesson08

import Data.Vect
import Data.Vect.Elem
import Data.String
import Decidable.Equality

%default total


-- removeElem : DecEq a => (value : a) -> (xs : Vect (S n) a) -> Vect n a
-- removeElem value (x :: xs) = case decEq value x of
--                                   (Yes prf) => xs
--                                   (No contra) => x :: removeElem value xs

elemTest : Elem "Mary" ["Peter", "Paul", "Mary"]
elemTest = There (There Here)

removeElem : (xs : Vect (S n) a) -> (prf : Elem _ xs) -> Vect n a
removeElem (x :: xs) Here = xs
removeElem (x :: []) (There later) = absurd later
removeElem (x :: (y :: xs)) (There later) = x :: removeElem (y :: xs) later

removeElem' : (value : a) -> (xs : Vect (S n) a) -> { auto prf : Elem value xs} -> Vect n a
removeElem' value (value :: xs) {prf = Here} = xs
removeElem' value (x :: []) {prf = There later} = absurd later
removeElem' value (x :: (y :: xs)) {prf = (There later)} = x :: removeElem' value (y :: xs)

notInNil : Elem value [] -> Void
notInNil Here impossible
notInNil (There later) impossible

notInTail : (value = x -> Void) -> (Elem value xs -> Void) -> Elem value (x :: xs) -> Void
notInTail notHere notThere Here = notHere Refl
notInTail notHere notThere (There later) = notThere later

isEl : DecEq a => (value : a) -> (xs : Vect n a) -> Dec (Elem value xs)
isEl value [] = No notInNil
isEl value (x :: xs) = case decEq value x of
                              (Yes Refl) => Yes Here
                              (No notHere) => case (isEl value xs) of
                                                   (Yes prf) => Yes (There prf)
                                                   (No notThere) => No (notInTail notHere notThere)

data Last : List a -> a -> Type where
    LastOne : Last [value] value
    LastCons : (prf : Last xs value) -> Last (x :: xs) value

notLastInNil : Last [] value -> Void
notLastInNil x impossible

aa : (x = value -> Void) -> Last [x] value -> Void
aa f LastOne = f Refl
aa _ (LastCons LastOne) impossible
aa _ (LastCons (LastCons prf)) impossible

bb : (Last (x :: xs) value -> Void) -> Last (y :: (x :: xs)) value -> Void
bb f (LastCons prf) = f prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No notLastInNil
isLast (x :: []) value = case decEq x value of
                            (Yes prf) => rewrite prf in Yes LastOne
                            (No contra) => No (aa contra)
isLast (x :: l @ (y :: xs)) value = case isLast l value of --case isLast (y :: xs) value of -- Yes $ LastCons (isLast (y :: xs) value)
                                        (Yes prf) => Yes (LastCons prf)
                                        (No contra) => No $ bb contra
                            -- (Yes prf) => Yes (LastCons (prf))
                            -- (No contra) => No (bb contra)
