module Lesson04

import Data.String
import Data.Vect
import System.REPL

%default total

-- readVect' : {l : Nat} -> IO (Vect l String)
-- readVect' = do x <- getLine
--                case x == "" of
--                  True => pure []
--                  False => do xs <- readVect'
--                              pure x :: xs

covering
readVect : IO (len ** Vect len String)
readVect = do x <- getLine
              case x == "" of
                 True => pure (_ ** [])
                 False => do (_ ** xs) <- readVect
                             pure (_ ** x :: xs)

dp : (len ** Vect len String)
dp = (2 ** ["labas", "medis"])

Position : Type
Position = (Double, Double)

-- adder 0 10 = 10
-- adder 1 10 10 = 20
-- adder 2 10 5 5 = 20

AdderType : (numargs: Nat) -> Type
AdderType 0 = Int
AdderType (S k) = (next : Int) -> AdderType k

adder : (numargs: Nat) -> (acc: Int) -> AdderType numargs
adder 0 acc = acc
adder (S k) acc = \next => adder k (acc + next)

-- printf("%s = %d", "el", 42)

data Format = Number Format
            | Str Format
            | Lit String Format
            | End

PrintfType : Format -> Type
PrintfType (Number x) = (i: Int) -> PrintfType x
PrintfType (Str x) = (s: String) -> PrintfType x
PrintfType (Lit str x) = (PrintfType x)
PrintfType End = String

printFmt : (fmt : Format) -> (acc: String) -> PrintfType fmt
printFmt (Number x) acc = \i => printFmt x (acc ++ show i)
printFmt (Str x) acc = \s => printFmt x (acc ++ s)
printFmt (Lit str x) acc = printFmt x (acc ++ str)
printFmt End acc = acc

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: xs) = Number (toFormat xs)
toFormat ('%' :: 's' :: xs) = Str (toFormat xs)
toFormat (x :: xs) = Lit (pack [x]) (toFormat xs)

-- printf "%s = %d" -> String -> Numb -> Strin
-- printf "%d" -> Numb -> Strin
-- printf "=" -> Strin

infixr 5 .+.

data Schema = SString
            | SInt
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
    constructor MkData
    schema : Schema
    size : Nat
    items : Vect size (SchemaType schema)

addToTail : Vect s t -> t -> Vect (S s) t
addToTail [] item = [item]
addToTail (x :: xs) item = x :: addToTail xs item

addToStore : (store : DataStore) -> (SchemaType (schema store)) -> DataStore
addToStore (MkData s size items) item =
     MkData s (S size) (addToTail items item)

display : {schema : Schema} -> SchemaType schema -> String
display {schema = SString} x = x
display {schema = SInt} x = show x
display {schema = (y .+. z)} (x, w) = "(" ++ display x ++ "," ++ display w ++ ")"

getEntry : (pos : Integer) -> (dataStore: DataStore) -> Maybe String
getEntry pos dataStore = case integerToFin pos (size dataStore) of
                              Nothing => Nothing
                              (Just x) => Just(display(index x (items dataStore)))

data Command : Schema -> Type where
    Add : (val : SchemaType s) -> Command s
    Get : (index : Integer) -> Command s
    ChangeType : (sch : Schema) -> Command s

Parser : Type -> Type
Parser result_type = (List Char -> Maybe (List Char, result_type))

parseChar : Char -> Parser Char
parseChar c = (\inp => case inp of
                            (c :: xs) => Just (xs, c)
                            _ => Nothing)

pairSwap : (a, b) -> (b, a)
pairSwap (x, y) = (y, x)

parseAlpha : Parser (List Char)
parseAlpha = (\inp => Just $ pairSwap $ span (?isAlphaNumeric) inp)

parseWithSchema' : List Char -> (sch : Schema) -> Maybe (SchemaType sch)
parseWithSchema' str SString = do (r1, _) <- parseChar '"' str
                                  (r2, str) <- parseAlpha r1
                                  (r3, _) <- parseChar '"' r2
                                  pure (pack str)
parseWithSchema' str SInt = ?hle_1
parseWithSchema' str (x .+. y) = ?hle_2

parseWithSchema : (str : String) -> (sch : Schema) -> Maybe (SchemaType sch)
parseWithSchema str sch = case parseWithSchema' (unpack str) sch of
                            ([], new_schema) => Just new_schema
                            _ => Nothing

parseCommand : String -> String -> (s : Schema) -> Maybe (Command s)
parseCommand "add" str sch = Just (Add (parseWithSchema str sch))
parseCommand "get" str _ = case all isDigit (unpack str) of
                              False => Nothing
                              True => Just (Get (cast str))
parseCommand "change" str _ = ?parseSchema
parseCommand _ _ _ = Nothing

parse : String -> (s: Schema) -> Maybe (Command s)
parse str = case span (/= ' ') str of
                        (cmd, arg) => parseCommand cmd (ltrim arg)

runCommand : (dataStore : DataStore) -> Command (schema dataStore) -> (String, DataStore)
runCommand dataStore (Add val) = ("Added", addToStore dataStore val)
runCommand dataStore (Get index) = case getEntry index dataStore of
                                        Nothing => ("Not found", dataStore)
                                        Just s => (s, dataStore)
runCommand dataStore (ChangeType sch) = case size dataStore of
                                            Z => ("Changed", MkData sch Z [])
                                            _ => ("Cannot change non-empty", dataStore)

runLine : String -> DataStore -> Maybe (String, DataStore)
runLine str dataStore = do cmd <- parse str (schema dataStore)
                           pure $ runCommand dataStore cmd

-- runCommand : {sch : Schema} -> Command sch -> DataStore -> (String, DataStore)
-- runCommand {sch} (Add value) dataStore = ("Added string", (addToStore dataStore ?hle))
-- runCommand _ _ = ?hle2
-- runCommand (Get i) dataStore = case tryIndex i (items dataStore) of
--      Nothing => ("Could not find index " ++ show i, dataStore)
--      Just item => ("Item at index " ++ show i ++ ": " ++ item, dataStore)

-- processInput : DataStore -> String -> (String, DataStore)
-- processInput dataStore input = case (parse input) of
--                                     Nothing => ("Unable to parse command", dataStore)
--                                     (Just x) => runCommand x dataStore

-- addNewline : DataStore -> String -> Maybe (String, DataStore)
-- addNewline dataStore str =
--   let (resultstr, resultDataStore) = processInput dataStore str
--   in
--      Just (resultstr ++ "\n", resultDataStore)

-- covering
-- main : IO ()
-- main = replWith (emptyDataStore) ">>> " addNewline 