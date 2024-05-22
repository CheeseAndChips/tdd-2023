module Compyler.Compyler

import Compyler.CodeObject

import Data.Vect
import Data.Vect.Elem
import Data.String
import Data.Bits
import System.File
import Data.Primitives.Views

%default total

CompileError : Type
CompileError = String

data PyBinaryOp = Add | Subtract | Multiply | Divide
data PyData = PyString String | PyInt Bits32 | PyNone
data PyConst = MkPyConst String PyData

data ElemInConsts : String -> Vect n PyConst -> Type where
  MkHere : ElemInConsts x (MkPyConst x d :: xs)
  MkThere : ElemInConsts x xs -> ElemInConsts x (y :: xs)

data PyVarHandle : Vect n PyConst -> Type where
    MkPyVarHandle : {xs : Vect n PyConst} -> (name : String) -> (i : ElemInConsts name xs) -> PyVarHandle xs
-- data PyData = PyConstData PyConst | PyVar PyVarHandle

data PyBytecode : (consts : Vect n PyConst) -> Type where
    RESUME : PyBytecode consts
    LOAD_CONST : (PyVarHandle consts) -> PyBytecode consts
    RETURN : PyBytecode consts
    BINARY_OP : (op : PyBinaryOp) -> PyBytecode consts
    -- MAKE_FUNCTION
    -- STORE_NAME Nat
    -- RETURN_CONST Nat

data PyOperation : Type -> (consts : Vect n PyConst) -> Type where
    PyReturnConst : (name : String) -> {auto prf : ElemInConsts name consts} -> PyOperation () consts
    PyReturnBinary : (c1 : String) -> (op : PyBinaryOp) -> (c2 : String) -> {auto prf1 : ElemInConsts c1 consts} -> {auto prf2 : ElemInConsts c2 consts} -> PyOperation () consts
    (>>=) : PyOperation a consts -> (a -> PyOperation b consts) -> PyOperation b consts
    (>>) : PyOperation a consts -> PyOperation b consts -> PyOperation b consts
    -- PyCreateConsts : (values : Vect n2 PyConst) -> PyOperation (Vect n2 (PyVarHandle values)) [] values
    -- PyAssign : (value : PyVarHandle) -> PyOperation PyVarHandle c1 c1
    -- PyBinary : (v1 : PyData) -> (op : PyBinaryOp) -> (v2 : PyData) -> PyOperation PyVarHandle consts

data PyProgram : (n_consts : Nat) -> (c : Vect n_consts PyConst) -> (op : PyOperation a c) -> Type where
  MkPyProgram : (c : Vect n PyConst) -> (op : PyOperation a c) -> PyProgram n c op

record PyCodeObject where
  constructor MkPyCodeObject
  argcount : Bits32
  posonlyargcount : Bits32
  kwonlyargcount : Bits32
  stacksize : Bits32
  flags : Bits32
  code : List (Bits8)
  consts : Vect n_consts PyConst
  names : Vect n_names String
  localsplusnames : Vect n_locals String
  localspluskinds : Vect n_locals Bits8
  filename : String
  name : String
  qualname : String
  firstlineno : Bits32
  linetable : Vect n_line Bits8
  exceptiontable : Vect n_exc Bits8

getFlag : Char -> Bits8
getFlag c = (cast c) .|. 0x80

interface PySerializable a where
  serializeWithoutFlag : a -> List Bits8
  serializeWithFlag : a -> List Bits8

toLittleEndian : Bits32 -> Vect 4 Bits8
toLittleEndian m = let b32 = [m .&. 0xff,
                             (shiftR m 8) .&. 0xff,
                             (shiftR m 16) .&. 0xff,
                             (shiftR m 24) .&. 0xff]
                   in map cast b32

getLenList : (len : Nat) -> List Bits8
getLenList len = let len = toLittleEndian (cast $ len)
                 in case len of
                          [x, 0, 0, 0] => [x]
                          xs           => toList xs

PySerializable Bits32 where
  serializeWithoutFlag x = toList (toLittleEndian x)
  serializeWithFlag x = getFlag 'i' :: serializeWithoutFlag x

PySerializable (List Bits8) where
  serializeWithoutFlag x = toList (toLittleEndian (cast $ length x)) ++ x
  serializeWithFlag x = getFlag 's' :: serializeWithoutFlag x

PySerializable (Vect _ Bits8) where
  serializeWithoutFlag x = serializeWithoutFlag $ toList x
  serializeWithFlag x = serializeWithFlag $ toList x

convertStrToBytes : AsList str -> List Bits8
convertStrToBytes [] = []
convertStrToBytes (c :: x) = (cast c) :: convertStrToBytes x

PySerializable String where
  serializeWithoutFlag x = getLenList (length x) ++ (convertStrToBytes $ asList x)
  serializeWithFlag x = (getFlag (if length x < 256 then 'Z' else 'a')) :: serializeWithoutFlag x

PySerializable PyData where
  serializeWithoutFlag (PyString str) = serializeWithoutFlag str
  serializeWithoutFlag (PyInt m) = serializeWithoutFlag m
  serializeWithoutFlag PyNone = []

  serializeWithFlag (PyString str) = serializeWithFlag str
  serializeWithFlag (PyInt i) = serializeWithFlag i
  serializeWithFlag PyNone = [cast 'N']

PySerializable PyConst where
  serializeWithoutFlag (MkPyConst _ x) = serializeWithoutFlag x
  serializeWithFlag (MkPyConst _ x) = serializeWithFlag x

PySerializable (Vect _ Bits32) where
  serializeWithoutFlag x = let len = toLittleEndian (cast $ length x)
                               len_buffer = case len of
                                                [x, 0, 0, 0] => [x]
                                                xs =>           toList xs
                           in len_buffer ++ (intercalate [] (toList $ map serializeWithFlag x))
  serializeWithFlag x = (getFlag (if length x < 256 then ')' else '(')) :: serializeWithoutFlag x

PySerializable (Vect _ String) where
  serializeWithoutFlag x = let len = toLittleEndian (cast $ length x)
                               len_buffer = case len of
                                                [x, 0, 0, 0] => [x]
                                                xs =>           toList xs
                           in len_buffer ++ (intercalate [] (toList $ map serializeWithFlag x))
  serializeWithFlag x = (getFlag (if length x < 256 then ')' else '(')) :: serializeWithoutFlag x

PySerializable (Vect _ PyConst) where
  serializeWithoutFlag x = let len = toLittleEndian (cast $ length x)
                               len_buffer = case len of
                                                [x, 0, 0, 0] => [x]
                                                xs =>           toList xs
                           in len_buffer ++ (intercalate [] (toList $ map serializeWithFlag x))
  serializeWithFlag x = (getFlag (if length x < 256 then ')' else '(')) :: serializeWithoutFlag x

PySerializable PyCodeObject where
  serializeWithoutFlag x = let xs = [serializeWithoutFlag (x.argcount),
                                     serializeWithoutFlag (x.posonlyargcount),
                                     serializeWithoutFlag (x.kwonlyargcount),
                                     serializeWithoutFlag (x.stacksize),
                                     serializeWithoutFlag (x.flags),
                                     serializeWithFlag (x.code),
                                     serializeWithFlag (x.consts),
                                     serializeWithFlag (x.names),
                                     serializeWithFlag (x.localsplusnames),
                                     serializeWithFlag (x.localspluskinds),
                                     serializeWithFlag (x.filename),
                                     serializeWithFlag (x.name),
                                     serializeWithFlag (x.qualname),
                                     serializeWithoutFlag (x.firstlineno),
                                     serializeWithFlag (x.linetable),
                                     serializeWithFlag (x.exceptiontable)]
                           in intercalate [] xs
  serializeWithFlag x = (getFlag 'c') :: serializeWithoutFlag x

getVarHandle : {xs, c : _} -> (i : ElemInConsts c xs) -> PyVarHandle xs
getVarHandle {c} i = MkPyVarHandle c i

getVarHandleIndex : ElemInConsts c xs -> Nat
getVarHandleIndex MkHere = 0
getVarHandleIndex (MkThere x) = S (getVarHandleIndex x)

appendBytecode : (a, List (PyBytecode c)) -> List (PyBytecode c) -> (a, List (PyBytecode c))
appendBytecode (x, y) xs = (x, xs ++ y)

turnToBytecode : (consts : Vect n PyConst) -> PyOperation a consts -> (a, List (PyBytecode consts))
turnToBytecode consts (PyReturnConst _ {prf}) = ((), [LOAD_CONST (getVarHandle prf), RETURN])
turnToBytecode consts (PyReturnBinary _ op _ {prf1} {prf2}) = ((), [LOAD_CONST (getVarHandle prf1), LOAD_CONST (getVarHandle prf2), BINARY_OP op, RETURN])
turnToBytecode consts (x >>= f) = let (a', code) = turnToBytecode consts x in appendBytecode (turnToBytecode consts (f a')) code
turnToBytecode consts (x >> y) = let (a', code) = turnToBytecode consts x in appendBytecode (turnToBytecode consts y) code

compile : PyProgram n c op -> (Vect n PyConst, List (PyBytecode c))
compile (MkPyProgram c op) = let (a, b) = turnToBytecode c op
                             in (c, [RESUME] ++ b)

serializeSingleInstruction : {xs : _} -> PyBytecode xs -> Either CompileError (List Bits8)
serializeSingleInstruction RESUME = Right [0x97, 0x00]
serializeSingleInstruction {xs} (LOAD_CONST (MkPyVarHandle _ i)) = let n = getVarHandleIndex i
                                                                   in if n < 256 then Right [0x64, cast n]
                                                                      else Left "Too many constants"
serializeSingleInstruction RETURN = Right [0x53, 0x00]
serializeSingleInstruction (BINARY_OP op) = Right [0x7a, 0x00, 0x00, 0x00]

createBinary : {xs : Vect n PyConst} -> List (PyBytecode xs) -> Either CompileError (List Bits8)
createBinary [] = Right []
createBinary (x :: ys) = do instr <- serializeSingleInstruction x
                            others <- createBinary ys
                            pure (instr ++ others)

getConsts : (prog : PyProgram n c _) -> Vect n PyConst
getConsts (MkPyProgram c _) = c

(:-) : String -> String -> PyConst
(:-) name c = MkPyConst name (PyString c)
private infix 5 :-

program = MkPyProgram [
              "Dievas" :- "H. Giedra",
              "DBVS3" :- "pasol nx"
          ] (do PyReturnBinary "Dievas" Add "DBVS3")

public export
main : IO ()
main = let (programConsts, compiled) = compile program
           binaryInstr = createBinary compiled
       in case binaryInstr of
               (Left err) => putStrLn err
               (Right xs) => putStrLn (show (serializeWithFlag $ MkPyCodeObject 0 0 0 2 3 xs programConsts [] [] [] "<string>" "func" "func" 1 [] []))

