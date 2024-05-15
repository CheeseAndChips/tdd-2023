module Lesson13.Stack

import Data.Vect

%default total

data StackCmd : Type -> Nat -> Nat -> Type where
    Push : Integer -> StackCmd () l (S l)
    Pop : StackCmd Integer (S l) l
    Top : StackCmd Integer (S l) (S l)
    Pure : a -> StackCmd a l l
    (>>=) : StackCmd a s1 s2 -> (a -> StackCmd b s2 s3) -> StackCmd b s1 s3
    (>>) : StackCmd a s1 s2 -> StackCmd b s2 s3 -> StackCmd b s1 s3
    GetStr : StackCmd String s s
    PutStr : String -> StackCmd () s s

testAdd : StackCmd Integer 0 0
testAdd = do    Push 17
                Push 13
                v1 <- Pop
                v2 <- Pop
                Pure (v1 + v2)

doAdd : StackCmd () (S (S l)) (S l)
doAdd = do  v1 <- Pop
            v2 <- Pop
            Push (v1 + v2)

run : (st : Vect h1 Integer) -> (StackCmd ty h1 h2) -> (ty, Vect h2 Integer)
run st (Push i) = ((), i :: st)
run (x :: xs) Pop = (x, xs)
run (x :: xs) Top = (x, x :: xs)
run st (Pure x) = (x, st)
run st (cmd >>= nxt) = let (res, st') = run st cmd in run st' (nxt res)
run st (cmd >> nxt) = let (_, st') = run st cmd in run st' nxt
run st GetStr = ("N/A", st)
run st (PutStr _) = ((), st)

runIO : (st : Vect h1 Integer) -> (StackCmd ty h1 h2) -> IO (ty, Vect h2 Integer)
runIO st (Push i) = pure ((), i :: st)
runIO (x :: xs) Pop = pure (x, xs)
runIO (x :: xs) Top = pure (x, x :: xs)
runIO st (Pure x) = pure (x, st)
runIO st (cmd >>= nxt) = do (res, st') <- runIO st cmd ; runIO st' (nxt res)
runIO st (cmd >> nxt) = do (_, st') <- runIO st cmd ; runIO st' nxt
runIO st GetStr = do ln <- getLine; pure(ln, st)
runIO st (PutStr s) = do putStr s; pure ((), st)

data StackIO : Nat -> Type where
    Do : StackCmd a h1 h2 -> (a -> Inf (StackIO h2)) -> StackIO h1

namespace StackDo
    export
    (>>=) : StackCmd a h1 h2 -> (a -> Inf (StackIO h2)) -> StackIO h1
    (>>=) = Do

    export
    (>>) : StackCmd a h1 h2 -> (Inf (StackIO h2)) -> StackIO h1
    (>>) x y = Do x (\_ => y)

data Fuel = Dry | More (Lazy Fuel)

covering
forever : Fuel
forever = More forever

execIO : Fuel -> Vect h Integer -> StackIO h -> IO ()
execIO Dry vec sio = pure ()
execIO (More fu) vec (Do act nxt) = do (res, vec') <- runIO vec act
                                       execIO fu vec' (nxt res)


data StackInput = Number Integer | Add

strToInput : String -> StackInput

mutual
    stackCalc : {h : Nat} -> StackIO h
    stackCalc = do  PutStr "> "
                    inp <- GetStr
                    case strToInput inp of
                        val => ?asd
