import Data.Vect

-- adding
makeRow : Num e => Vect col e -> Vect col e -> Vect col e
makeRow [] [] = []
makeRow (x :: xs) (y :: ys) = x+y :: makeRow xs ys

addMatrics : Num e => Vect row (Vect col e) -> 
                      Vect row (Vect col e) ->
                      Vect row (Vect col e)
addMatrics [] [] = []
addMatrics (x :: xs) (y :: ys) = makeRow x y :: addMatrics xs ys


-- transposing
transposeHelp : Vect n e -> Vect n (Vect len e) -> Vect n (Vect (S len) e)
transposeHelp [] [] = []
transposeHelp (x :: xs) (y :: ys) = (x :: y) :: transposeHelp xs ys

empties : {n : Nat} -> Vect n (Vect 0 e)
empties {n = 0} = []
empties {n = (S k)} = [] :: empties {n=k}

transposeMat : {n:Nat} -> Vect m (Vect n e) -> Vect n (Vect m e)
transposeMat [] = empties
transposeMat (x :: xs) = let transposed = (transposeMat xs) in
                             transposeHelp x transposed

-- multiplying
-- vienaCele : Num e => Vect m e -> Vect m e -> e
-- vienaCele [] [] = 0
-- vienaCele (x :: xs) (y :: ys) = x*y + vienaCele xs ys
-- 
-- vienaEilute : Num e => Vect m e -> Vect p (Vect m e) ->  Vect p e
-- vienaEilute xs [] = []
-- vienaEilute xs (x :: ys) = vienaCele x xs :: vienaEilute xs ys
-- 
-- mulMatrics' : Num e => {n: Nat} -> Vect n (Vect m e) ->
--                                    Vect p (Vect m e) ->
--                                    Vect n (Vect p e)
-- mulMatrics' [] ys = []
-- mulMatrics' (x :: xs) ys = vienaEilute x ys :: mulMatrics' xs ys
-- 
-- mulMatrics : Num e => {n: Nat} -> {m: Nat} -> {p: Nat} -> Vect n (Vect m e) ->
--                                                           Vect m (Vect p e) ->
--                                                           Vect n (Vect p e)
-- mulMatrics xs ys = mulMatrics' xs (transposeMat ys)


vienaCele : Num e => Vect m e -> Vect m e -> e
vienaCele [] [] = 0
vienaCele (x :: xs) (y :: ys) = x*y + vienaCele xs ys

vienasStulpelis : Num e => Vect m e -> Vect p (Vect m e) -> Vect p e
vienasStulpelis xs [] = []
vienasStulpelis xs (x :: ys) = vienaCele x xs :: vienasStulpelis xs ys

mulMatrics' : Num e => {n: Nat} -> Vect n (Vect m e) ->
                                   Vect p (Vect m e) ->
                                   Vect n (Vect p e)
mulMatrics' [] [] = []
mulMatrics' [] (x :: xs) = []
mulMatrics' (x :: xs) ys = vienasStulpelis x ys :: mulMatrics' xs ys

mulMatrics : Num e => {n: Nat} -> {m: Nat} -> {p: Nat} -> Vect n (Vect m e) ->
                                                          Vect m (Vect p e) ->
                                                          Vect n (Vect p e)
mulMatrics xs ys = mulMatrics' xs (transposeMat ys)

-- samples
added = addMatrics [[1,2,3],[4,5,6]] [[7,8,9],[1,6,3]]
mulled = mulMatrics [[1, 6], [2, 5], [3, 4]] [[1, 2, 3, 4], [4, 5, 6, 5]]