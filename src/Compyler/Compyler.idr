module Compyler.Compyler

import Compyler.CodeObject
import Compyler.Serialize

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
data PyVar = MkPyVar String

record PyContext where
  constructor MkPyContext
  consts : Vect n_consts PyConst
  vars : Vect n_vars PyVar

-- constProofType : (const : PyConst) -> (context : PyContext) -> Type

getConstStringVect : Vect n PyConst -> Vect n String
getConstStringVect [] = []
getConstStringVect ((MkPyConst str _) :: xs) = str :: getConstStringVect xs

constElemPrf : String -> PyContext -> Type
constElemPrf name context = Elem name (getConstStringVect (consts context))

getVarStringVect : Vect n PyVar -> Vect n String
getVarStringVect [] = []
getVarStringVect ((MkPyVar str) :: xs) = str :: getVarStringVect xs

varElemPrf : String -> PyContext -> Type
varElemPrf name context = Elem name (getVarStringVect (vars context))

-- getPyRHSProofType : (rhs : PyRHS) -> (context : PyContext) -> Type
-- getPyRHSProofType (MkPyRHSConst x) context = constProofType x -- Elem x consts
-- getPyRHSProofType (MkPyRHSVar x) context = ?asdasd --Elem x vars

data PyBytecode : (context : PyContext) -> Type where
    RESUME : PyBytecode _
    LOAD_CONST : (c : String) -> (prf : constElemPrf c context) -> PyBytecode context
    LOAD_FAST_CHECK : (v : String) -> (prf : varElemPrf v context) -> PyBytecode context
    STORE_FAST : (v : String) -> (prf : varElemPrf v context) -> PyBytecode context
    RETURN : PyBytecode _
    BINARY_OP : (op : PyBinaryOp) -> PyBytecode _
    -- MAKE_FUNCTION
    -- STORE_FAST Nat
    -- RETURN_CONST Nat

mutual
  data PyRHS : (context : PyContext) -> Type where
    MkPyRHSConst : (c : String) -> (prf : constElemPrf c context) -> PyRHS context
    MkPyRHSVar : (v : String) -> (prf : varElemPrf v context) -> PyRHS context
    MkPyRHSBinary : (rhs1 : PyRHS context) -> (op : PyBinaryOp) -> (rhs2 : PyRHS context) -> PyRHS context
  
  data PyOperation : Type -> (context : PyContext) -> Type where
      -- PyLoadConst : (c : String) -> {auto prf : constElemPrf c context} -> PyOperation n (S n) context
      -- PyLoadVar : (v : String) -> {auto prf : varElemPrf v context} -> PyOperation n (S n) context
      -- PyStoreVar : (v : String) -> (rhs : PyRHS) -> PyOperation (S n) n context
      PyLoadConst : (c : String) -> {auto prf : constElemPrf c context} -> PyOperation (PyRHS context) context
      PyLoadVar : (v : String) -> {auto prf : varElemPrf v context} -> PyOperation (PyRHS context) context
      PyReturn : (rhs : PyRHS context) -> PyOperation () context
      PyAssignToVar : (v : String) -> (rhs : PyRHS context) -> {auto prf : varElemPrf v context} -> PyOperation () context
      (>>=) : PyOperation a context -> (a -> PyOperation b context) -> PyOperation b context
      (>>) : PyOperation a context -> PyOperation b context -> PyOperation b context
 
data PyProgram : (context : PyContext) -> Type where
  MkPyProgram : (context : PyContext) -> (op : PyOperation a context) -> PyProgram context

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
  localsplusnames : Vect n_locals PyVar
  localspluskinds : Vect n_locals Bits8
  filename : String
  name : String
  qualname : String
  firstlineno : Bits32
  linetable : Vect n_line Bits8
  exceptiontable : Vect n_exc Bits8

-- getVarHandle : {xs, c : _} -> (i : ElemInConsts c xs) -> PyVarHandle xs
-- getVarHandle {c} i = MkPyVarHandle c i
-- 
-- getVarHandleIndex : ElemInConsts c xs -> Nat
-- getVarHandleIndex MkHere = 0
-- getVarHandleIndex (MkThere x) = S (getVarHandleIndex x)


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
                                     serializeWithFlag (map (\(MkPyVar s) => s) x.localsplusnames),
                                     serializeWithFlag (x.localspluskinds),
                                     serializeWithFlag (x.filename),
                                     serializeWithFlag (x.name),
                                     serializeWithFlag (x.qualname),
                                     serializeWithoutFlag (x.firstlineno),
                                     serializeWithFlag (x.linetable),
                                     serializeWithFlag (x.exceptiontable)]
                           in intercalate [] xs
  serializeWithFlag x = (getFlag 'c') :: serializeWithoutFlag x

maxList : Vect (S n) Nat -> Nat
maxList [x] = x
maxList (x :: (y :: xs)) = max (maxList (y :: xs)) x

-- stackUsage : {n1, n2 : _} -> Nat -> PyOperation n1 n2 context -> Nat
-- stackUsage k (x >>= f) = maxList [n1, n2, k, stackUsage k x]
-- stackUsage k (x >> y) = ?asdasd_6
-- stackUsage k _ = maxList [n1, n2, k]

getRHSBytecode : (context : PyContext) -> PyRHS context -> List (PyBytecode context)
getRHSBytecode context (MkPyRHSConst c {prf}) = [LOAD_CONST c prf]
getRHSBytecode context (MkPyRHSVar v {prf}) = [LOAD_FAST_CHECK v prf]
getRHSBytecode context (MkPyRHSBinary rhs1 op rhs2) = getRHSBytecode context rhs1 ++ getRHSBytecode context rhs2 ++ [BINARY_OP op]

appendBytecode : (a, List (PyBytecode context)) -> List (PyBytecode context) -> (a, List (PyBytecode context))
appendBytecode (x, xs) ys = (x, ys ++ xs)

turnToBytecode : (context : PyContext) -> PyOperation a context -> (a, List (PyBytecode context))
turnToBytecode context (PyLoadConst c {prf}) = (MkPyRHSConst c prf, [])
turnToBytecode context (PyLoadVar v {prf}) = (MkPyRHSVar v prf, [])
turnToBytecode context (PyReturn rhs) = ((), getRHSBytecode context rhs ++ [RETURN])
turnToBytecode context (PyAssignToVar v rhs {prf}) = ((), getRHSBytecode context rhs ++ [STORE_FAST v prf])
turnToBytecode context (x >>= f) = let (a', code) = turnToBytecode context x in appendBytecode (turnToBytecode context (f a')) code
turnToBytecode context (x >> y) = let (a', code) = turnToBytecode context x in appendBytecode (turnToBytecode context y) code
-- turnToBytecode context (PyReturn rhs) = getRHSBytecode context rhs ++ [RETURN]
-- turnToBytecode context (PyAssignToVar v rhs {prf}) = getRHSBytecode context rhs ++ [STORE_FAST v prf]
-- turnToBytecode context (x >>= f) = let code = turnToBytecode context x in turnToBytecode context (f ()) ++ code
-- turnToBytecode context (x >> y) = let code = turnToBytecode context x in turnToBytecode context y ++ code

-- turnToBytecode consts (PyReturnConst _ {prf}) = ((), [LOAD_CONST (getVarHandle prf), RETURN])
-- turnToBytecode consts (PyReturnBinary _ op _ {prf1} {prf2}) = ((), [LOAD_CONST (getVarHandle prf1), LOAD_CONST (getVarHandle prf2), BINARY_OP op, RETURN])
-- turnToBytecode consts (x >>= f) = let (a', code) = turnToBytecode consts x in appendBytecode (turnToBytecode consts (f a')) code
-- turnToBytecode consts (x >> y) = let (a', code) = turnToBytecode consts x in appendBytecode (turnToBytecode consts y) code
-- 

compile : PyProgram context -> (PyContext, List (PyBytecode context))
compile (MkPyProgram context op) = let (a, b) = turnToBytecode context op
                                   in (context, [RESUME] ++ b)

tryCastingElem : Elem _ _ -> Either CompileError (Bits8)
tryCastingElem x = let n = finToNat $ elemToFin x
                   in if n < 256 then Right $ cast n
                   else Left "Too many Elem"

serializeSingleInstruction : PyBytecode _ -> Either CompileError (List Bits8)
serializeSingleInstruction RESUME = pure [0x97, 0x00]
serializeSingleInstruction (LOAD_CONST _ prf) = do n <- tryCastingElem prf
                                                   pure [0x64, n]
serializeSingleInstruction (LOAD_FAST_CHECK _ prf) = do n <- tryCastingElem prf
                                                        pure [0x65, n]
serializeSingleInstruction (STORE_FAST _ prf) = do n <- tryCastingElem prf
                                                   pure [0x5a, n]
serializeSingleInstruction RETURN = pure [0x53, 0x00]
serializeSingleInstruction (BINARY_OP op) = pure [0x7a, 0x00, 0x00, 0x00]

createBinary : List (PyBytecode _) -> Either CompileError (List Bits8)
createBinary [] = Right []
createBinary (x :: ys) = do instr <- serializeSingleInstruction x
                            others <- createBinary ys
                            pure (instr ++ others)

(:-) : String -> Bits32 -> PyConst
(:-) name c = MkPyConst name (PyInt c)
private infix 5 :-

-- makeProgram : Vect n PyConst -> Vect m PyVar -> PyOperation context -> (context : PyContext ** PyOperation context)
-- makeProgram xs ys = let ctx = MkPyContext xs ys
--                     in (ctx ** ?asdkjsdfgh)

ctx : PyContext
ctx = MkPyContext ["c1" :- 10,
                   "c2" :- 20] [MkPyVar "v1"]

program = MkPyProgram ctx $ do c1 <- PyLoadConst "c1"
                               c2 <- PyLoadConst "c2"
                               v1 <- PyLoadVar "v1"
                               PyAssignToVar "v1" (MkPyRHSBinary c1 Add c2)
                               PyAssignToVar "v1" (MkPyRHSBinary v1 Add v1)
                               PyReturn v1

ctst = (the (PyRHS ctx) $ MkPyRHSConst "c1" Here)
vtst = (the (PyRHS ctx) $ MkPyRHSVar "v1" Here)
btst = (the (PyRHS ctx) $ (MkPyRHSBinary (MkPyRHSConst "c1" Here) Add (MkPyRHSVar "v1" Here)))

-- containsDuplicate : (xs : Vect n Nat) -> Bool
-- containsDuplicate [] = False
-- containsDuplicate (x :: xs) = (containsDuplicate xs) || (hasAny [x] xs)
-- 
-- data TestUnique : Type where
--   MkTestUnique : (xs : Vect n Nat) -> {auto prf : containsDuplicate xs = False} -> TestUnique
-- 
-- lol = MkTestUnique [1, 2]

public export
main : IO ()
main = let ((MkPyContext consts vars), compiled) = compile program
           binaryInstr = createBinary compiled
       in case binaryInstr of
               (Left err) => putStrLn err
               (Right xs) => putStrLn (show (serializeWithFlag $ MkPyCodeObject 0 0 0 2 3 xs consts (map (\(MkPyVar s) => s) vars) vars (map (const 0x20) vars) "<string>" "func" "func" 1 [] []))
