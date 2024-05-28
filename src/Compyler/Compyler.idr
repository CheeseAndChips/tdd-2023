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

data PyBinaryOp = Add | Subtract | Multiply | Divide | GT | LT | EQ
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

data PyVarHandle : (context : PyContext) -> Type where
  MkPyVarHandle : (v : String) -> (prf : varElemPrf v context) -> PyVarHandle context

getNameFromHandle : PyVarHandle _ -> String
getNameFromHandle (MkPyVarHandle v _) = v

data PyBytecode : (context : PyContext) -> Type where
    RESUME : PyBytecode _
    LOAD_CONST : (c : String) -> (prf : constElemPrf c context) -> PyBytecode context
    LOAD_FAST_CHECK : (v : String) -> (prf : varElemPrf v context) -> PyBytecode context
    STORE_FAST : (v : String) -> (prf : varElemPrf v context) -> PyBytecode context
    RETURN : PyBytecode _
    BINARY_OP : (op : PyBinaryOp) -> PyBytecode _
    JUMP_FORWARD : (cnt : Nat) -> PyBytecode _
    POP_JUMP_IF_FALSE : (cnt : Nat) -> PyBytecode _
    -- MAKE_FUNCTION
    -- STORE_FAST Nat
    -- RETURN_CONST Nat

mutual
  data PyRHS : (context : PyContext) -> Type where
    MkPyRHSConst : (c : String) -> (prf : constElemPrf c context) -> PyRHS context
    MkPyRHSVar : PyVarHandle context -> PyRHS context
    MkPyRHSBinary : (rhs1 : PyRHS context) -> (op : PyBinaryOp) -> (rhs2 : PyRHS context) -> PyRHS context
  
  data PyOperation : Type -> (context : PyContext) -> Type where
      PyLoadConst : (c : String) -> {auto prf : constElemPrf c context} -> PyOperation (PyRHS context) context
      PyLoadVar : (v : String) -> {auto prf : varElemPrf v context} -> PyOperation (PyVarHandle context) context
      PyReturn : (rhs : PyRHS context) -> PyOperation () context
      PyAssignToVar : (v : PyVarHandle context) -> (rhs : PyRHS context) -> PyOperation () context
      PyIf : (cond : PyRHS context) -> (true_op : PyOperation () context) -> (false_op : PyOperation () context) -> PyOperation () context
      Pure : a -> PyOperation a context
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
getRHSBytecode context (MkPyRHSConst c prf) = [LOAD_CONST c prf]
getRHSBytecode context (MkPyRHSVar (MkPyVarHandle v prf)) = [LOAD_FAST_CHECK v prf]
getRHSBytecode context (MkPyRHSBinary rhs1 op rhs2) = getRHSBytecode context rhs1 ++ getRHSBytecode context rhs2 ++ [BINARY_OP op]

appendBytecode : (a, List (PyBytecode context)) -> List (PyBytecode context) -> (a, List (PyBytecode context))
appendBytecode (x, xs) ys = (x, ys ++ xs)

getInstructionLength : (PyBytecode _) -> Nat
getInstructionLength RESUME = 2
getInstructionLength (LOAD_CONST c prf) = 2
getInstructionLength (LOAD_FAST_CHECK v prf) = 2
getInstructionLength (STORE_FAST v prf) = 2
getInstructionLength RETURN = 2
getInstructionLength (BINARY_OP op) = 4
getInstructionLength (JUMP_FORWARD cnt) = 2
getInstructionLength (POP_JUMP_IF_FALSE cnt) = 2

getInstrListLen : List (PyBytecode _) -> Nat
getInstrListLen xs = sum (map getInstructionLength xs)

turnToBytecode : (context : PyContext) -> PyOperation a context -> (a, List (PyBytecode context))
turnToBytecode context (PyLoadConst c {prf}) = (MkPyRHSConst c prf, [])
turnToBytecode context (PyLoadVar v {prf}) = (MkPyVarHandle v prf, [])
turnToBytecode context (PyReturn rhs) = ((), getRHSBytecode context rhs ++ [RETURN])
turnToBytecode context (PyAssignToVar (MkPyVarHandle v prf) rhs) = ((), getRHSBytecode context rhs ++ [STORE_FAST v prf])
turnToBytecode context (PyIf cond true_op false_op) = let (_, true_comp) = turnToBytecode context true_op
                                                          (_, false_comp) = turnToBytecode context false_op
                                                          true_comp' = true_comp ++ [JUMP_FORWARD (getInstrListLen false_comp `div` 2)]
                                                      in ((), getRHSBytecode context cond ++
                                                              [POP_JUMP_IF_FALSE (getInstrListLen true_comp' `div` 2)] ++ 
                                                              true_comp' ++
                                                              false_comp)
turnToBytecode context (Pure x) = (x, [])
turnToBytecode context (x >>= f) = let (a', code) = turnToBytecode context x in appendBytecode (turnToBytecode context (f a')) code
turnToBytecode context (x >> y) = let (a', code) = turnToBytecode context x in appendBytecode (turnToBytecode context y) code

compile : PyProgram context -> (PyContext, List (PyBytecode context))
compile (MkPyProgram context op) = let (a, b) = turnToBytecode context op
                                   in (context, [RESUME] ++ b)

tryCastingElem : Elem _ _ -> Bits8
tryCastingElem x = cast (finToNat $ elemToFin x)

serializeSingleInstruction : PyBytecode _ -> List Bits8
serializeSingleInstruction RESUME = [0x97, 0x00]
serializeSingleInstruction (LOAD_CONST _ prf) = [0x64, tryCastingElem prf]
serializeSingleInstruction (LOAD_FAST_CHECK _ prf) = [0x65, tryCastingElem prf]
serializeSingleInstruction (STORE_FAST _ prf) = [0x5a, tryCastingElem prf]
serializeSingleInstruction RETURN = [0x53, 0x00]
serializeSingleInstruction (BINARY_OP Add) = [0x7a, 0x00, 0x00, 0x00]
serializeSingleInstruction (BINARY_OP Subtract) = [0x7a, 0x0a, 0x00, 0x00]
serializeSingleInstruction (BINARY_OP Multiply) = [0x7a, 0x05, 0x00, 0x00]
serializeSingleInstruction (BINARY_OP Divide) = [0x7a, 0x02, 0x00, 0x00]
serializeSingleInstruction (BINARY_OP GT) = [0x6b, 0x44, 0x00, 0x00]
serializeSingleInstruction (BINARY_OP LT) = [0x6b, 0x02, 0x00, 0x00]
serializeSingleInstruction (BINARY_OP EQ) = [0x6b, 0x28, 0x00, 0x00]
serializeSingleInstruction (JUMP_FORWARD cnt) = [0x6e, cast cnt]
serializeSingleInstruction (POP_JUMP_IF_FALSE cnt) = [0x72, cast cnt]

instrLenProof : (bc : PyBytecode _) -> (length (serializeSingleInstruction bc)) = (getInstructionLength bc)
instrLenProof RESUME = Refl
instrLenProof (LOAD_CONST c prf) = Refl
instrLenProof (LOAD_FAST_CHECK v prf) = Refl
instrLenProof (STORE_FAST v prf) = Refl
instrLenProof RETURN = Refl
instrLenProof (BINARY_OP Add) = Refl
instrLenProof (BINARY_OP Subtract) = Refl
instrLenProof (BINARY_OP Multiply) = Refl
instrLenProof (BINARY_OP Divide) = Refl
instrLenProof (BINARY_OP GT) = Refl
instrLenProof (BINARY_OP LT) = Refl
instrLenProof (BINARY_OP EQ) = Refl
instrLenProof (JUMP_FORWARD cnt) = Refl
instrLenProof (POP_JUMP_IF_FALSE cnt) = Refl

createBinary : List (PyBytecode _) -> List Bits8
createBinary [] = []
createBinary (x :: ys) = serializeSingleInstruction x ++ createBinary ys

fromInteger : Integer -> PyData
fromInteger x = PyInt (cast x)

fromString : String -> PyData
fromString str = PyString str

(-=) : String -> PyData -> PyConst
(-=) name c = MkPyConst name c
private infix 1 -=

(.=) : PyVarHandle context -> PyRHS context -> PyOperation () context 
(.=) h y = PyAssignToVar h y
private infix 1 .=

initConst : (c : String) -> {auto prf : constElemPrf c context} -> PyOperation (PyRHS context) context
initConst c = PyLoadConst c

init : (v : String) -> (c : PyRHS context) -> {auto prf : varElemPrf v context} -> PyOperation (PyVarHandle context) context
init v c = do v' <- PyLoadVar v
              v' .= c
              Pure v'

Cast (PyVarHandle context) (PyRHS context) where
  cast h = MkPyRHSVar h

-- PyIf : (cond : PyRHS context) -> (true_op : PyOperation () context) -> (false_op : PyOperation () context) -> PyOperation () context
doif : (cond : PyRHS context) -> (true_op : PyOperation () context) -> (false_op : PyOperation () context) -> PyOperation () context
doif cond true_op false_op = PyIf cond true_op false_op

(.==) : (Cast a (PyRHS context), Cast b (PyRHS context)) => a -> b -> PyRHS context
(.==) x y = MkPyRHSBinary (cast x) EQ (cast y)
private infix 7 .==

(.>) : (Cast a (PyRHS context), Cast b (PyRHS context)) => a -> b -> PyRHS context
(.>) x y = MkPyRHSBinary (cast x) GT (cast y)
private infix 5 .>

(.<) : (Cast a (PyRHS context), Cast b (PyRHS context)) => a -> b -> PyRHS context
(.<) x y = MkPyRHSBinary (cast x) LT (cast y)
private infix 5 .<

(.+) : (Cast a (PyRHS context), Cast b (PyRHS context)) => a -> b -> PyRHS context
(.+) x y = MkPyRHSBinary (cast x) Add (cast y)
private infix 5 .+

(.-) : (Cast a (PyRHS context), Cast b (PyRHS context)) => a -> b -> PyRHS context
(.-) x y = MkPyRHSBinary (cast x) Subtract (cast y)
private infix 8 .-

(.*) : (Cast a (PyRHS context), Cast b (PyRHS context)) => a -> b -> PyRHS context
(.*) x y = MkPyRHSBinary (cast x) Multiply (cast y)
private infix 9 .*

(.//) : (Cast a (PyRHS context), Cast b (PyRHS context)) => a -> b -> PyRHS context
(.//) x y = MkPyRHSBinary (cast x) Divide (cast y)
private infix 9 .//

return : Cast a (PyRHS context) => a -> PyOperation () context
return x = PyReturn (cast x)

ctx : PyContext
ctx = MkPyContext ["c1" -= 10,
                   "c2" -= 20] [MkPyVar "v1"]

program = MkPyProgram ctx $ do c1 <- initConst "c1"
                               c2 <- initConst "c2"
                               v1 <- init "v1" c1
                               doif (c1) (v1 .= c1 .* c2) (v1 .= c1 .- c2)
                               return v1

public export
main : IO ()
main = let ((MkPyContext consts vars), compiled) = compile program
           binaryInstr = createBinary compiled
       in putStrLn (show (serializeWithFlag $ MkPyCodeObject 0 0 0 2 3 binaryInstr consts (map (\(MkPyVar s) => s) vars) vars (map (const 0x20) vars) "<string>" "func" "func" 1 [] []))

  -- containsDuplicate : (xs : Vect n Nat) -> Bool
  -- containsDuplicate [] = False
  -- containsDuplicate (x :: xs) = (containsDuplicate xs) || (hasAny [x] xs)
  -- 
  -- data TestUnique : Type where
  --   MkTestUnique : (xs : Vect n Nat) -> {auto prf : containsDuplicate xs = False} -> TestUnique
  -- 
  -- lol = MkTestUnique [1, 2]

