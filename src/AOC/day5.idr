import Data.Vect
import Data.String
import Data.List.Elem
import Decidable.Equality
import System.File.ReadWrite

%default total

data MapRange : Type where
  MkMapRange : (dest_start : Nat) -> (source_start : Nat) -> (len : Nat) -> MapRange

data FertilizerMap : String -> String -> Type where
  MkFertilizerMap : (in_type : String) -> (out_type : String) -> FertilizerMap in_type out_type

data Hide : Type where
  MkHide : FertilizerMap a b -> Hide

record InputData where
  constructor MkInputData
  seeds : Vect n_seeds Nat
  maps : Vect n_maps Hide

extractFromMap : (x : String) -> Vect n Hide -> Maybe (b : String ** FertilizerMap x b)
extractFromMap x [] = Nothing
extractFromMap x ((MkHide mp@(MkFertilizerMap a' b')) :: xs) = case decEq a' x of
                                                                    (Yes prf) => rewrite (sym prf) in Just (b' ** mp)
                                                                    (No contra) => extractFromMap x xs

data ElemHide : (x : FertilizerMap in_type out_type) -> (xs : Vect n Hide) -> Type where
  HereHide : ElemHide x (MkHide x :: xs)
  ThereHide : ElemHide x xs -> ElemHide x (y :: xs)

willExtractExisting : (x : String) -> (xs : Vect n Hide) -> (y : FertilizerMap x a ** ElemHide y xs) -> (extractFromMap x xs) = Just (a : String ** FertilizerMap x a)
willExtractExisting _ [] (_ ** ThereHide y) impossible
willExtractExisting x ((MkHide _) :: xs) ((fst ** HereHide)) = case decEq (extractFromMap x xs) ?asg of
                                                                    asd => ?askjfdh
willExtractExisting x (z :: xs) ((fst ** (ThereHide y))) = ?willExtractExisting_rhs_4
 -- (y : FertilizerMap x a ** ElemHide y xs) -> FertilizerMap x a

splitByEmptyLine' : (acc : List String) -> (xs : List String) -> List (List String)
splitByEmptyLine' acc [] = [acc]
splitByEmptyLine' acc ("" :: xs) = acc :: (splitByEmptyLine' [] (xs))
splitByEmptyLine' acc (x :: xs) = splitByEmptyLine' (acc ++ [x]) xs

splitByEmptyLine : (xs : List String) -> List (List String)
splitByEmptyLine = splitByEmptyLine' []

parseInputData : List String -> InputData

solveDay1 : String -> String
solveDay1 xs = case splitByEmptyLine (lines xs) of
                    (seeds :: maps) => ?asdasdkjh
                    _ => ?not_good

covering
public export
main : IO ()
main = do
  a <- readFile "day5.sample.txt"
  case a of
       (Left x) => putStrLn $ "Failed reading input: " ++ show x
       (Right x) => putStrLn $ show (solveDay1 x)

