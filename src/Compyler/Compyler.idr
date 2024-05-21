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
data PyConst = PyString String | PyInt Bits32 | PyNone
data PyVarHandle : Vect n PyConst -> Type where
    MkPyVarHandle : {xs : Vect n PyConst} -> (const : PyConst) -> (i : Elem const xs) -> PyVarHandle xs
-- data PyData = PyConstData PyConst | PyVar PyVarHandle

data PyBytecode : (consts : Vect n PyConst) -> Type where
    RESUME : PyBytecode consts
    LOAD_CONST : (PyVarHandle consts) -> PyBytecode consts
    RETURN : PyBytecode consts
    -- MAKE_FUNCTION
    -- STORE_NAME Nat
    -- RETURN_CONST Nat
    -- BINARY_OP PyBinaryOp

data PyOperation : Type -> (consts_old : Vect n1 PyConst) -> (consts_new : Vect n2 PyConst) -> Type where
    -- PyCreateConst : (value : PyConst) -> PyOperation (PyVarHandle (value :: c1)) c1 (value :: c1)
    PyCreateConsts : (values : Vect n2 PyConst) -> PyOperation (Vect n2 (PyVarHandle values)) [] values
    PyReturn : (value : PyVarHandle c) -> PyOperation () c c
    (>>=) : PyOperation a c1 c2 -> (a -> PyOperation b c2 c2) -> PyOperation b c1 c2
    (>>) : PyOperation a c1 c2 -> PyOperation b c2 c3 -> PyOperation b c1 c3
    -- PyAssign : (value : PyVarHandle) -> PyOperation PyVarHandle c1 c1
    -- PyBinary : (v1 : PyData) -> (op : PyBinaryOp) -> (v2 : PyData) -> PyOperation PyVarHandle consts

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

PySerializable PyConst where
  serializeWithoutFlag (PyString str) = serializeWithoutFlag str
  serializeWithoutFlag (PyInt m) = serializeWithoutFlag m
  serializeWithoutFlag PyNone = []

  serializeWithFlag (PyString str) = serializeWithFlag str
  serializeWithFlag (PyInt i) = serializeWithFlag i
  serializeWithFlag PyNone = [cast 'N']

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


serializeCodeObject : PyCodeObject -> Either CompileError (List Bits8)
serializeCodeObject x = ?serializeCodeObject_rhs

getVarHandleIndex : {xs : Vect n _} -> PyVarHandle xs -> Nat
getVarHandleIndex (MkPyVarHandle _ i) = finToNat $ elemToFin i

createVarHandles : (xy : Vect n PyConst) -> Vect n (PyVarHandle xy)
createVarHandles [] = []
createVarHandles (x :: xs) = (MkPyVarHandle x Here :: (map (\(MkPyVarHandle y ys) => MkPyVarHandle y (There ys)) (createVarHandles xs)))

turnToBytecode : (consts : Vect n PyConst) -> PyOperation a xs xy -> (a, List (PyBytecode xy))
turnToBytecode consts (PyCreateConsts xy) = (createVarHandles xy, [])
turnToBytecode consts (PyReturn value) = ((), [LOAD_CONST value, RETURN])
turnToBytecode consts (x >>= f) = let (a', code) = turnToBytecode consts x in turnToBytecode consts (f a')
turnToBytecode consts (x >> y) = let (a', code) = turnToBytecode consts x in turnToBytecode consts y

compile : {n : _} -> {xs : Vect n PyConst} -> PyOperation () [] xs -> List (PyBytecode xs)
compile {xs} x = let (a, b) = turnToBytecode xs x in [RESUME] ++ b

serializeSingleInstruction : {xs : _} -> PyBytecode xs -> Either CompileError (List Bits8)
serializeSingleInstruction RESUME = Right [0x97, 0x00]
serializeSingleInstruction {xs} (LOAD_CONST x) = let n = getVarHandleIndex x
                                                 in if n < 256 then Right [0x64, cast n]
                                                    else Left "Too many constants"
serializeSingleInstruction RETURN = Right [0x53, 0x00]

createBinary : {xs : Vect n PyConst} -> List (PyBytecode xs) -> Either CompileError (List Bits8)
createBinary [] = Right []
createBinary (x :: ys) = do instr <- serializeSingleInstruction x
                            others <- createBinary ys
                            pure (instr ++ others)

program =  do consts <- PyCreateConsts [
                            PyString "sveikas",
                            PyString "pasauli",
                            PyInt 42
                        ]
              PyReturn (index 2 consts)

getConsts : {ys : Vect n PyConst} -> PyOperation () [] ys -> Vect n PyConst
getConsts _ = ys

compiled = compile program
binaryInstr = createBinary compiled
programConsts = getConsts program

main : IO ()
main = case binaryInstr of
               (Left err) => putStrLn err
               (Right xs) => putStrLn (show (serializeWithFlag $ MkPyCodeObject 0 0 0 2 3 xs programConsts [] [] [] "<string>" "func" "func" 1 [] []))

