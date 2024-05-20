module Compyler.Compyler

import Data.Vect
import Data.Vect.Elem

%default total

data PyBinaryOp = Add | Subtract | Multiply | Divide
data PyConst = PyString String | PyInt Integer | PyNone
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

data PySerializedBytecode : (consts : Vect n PyConst) -> Type where
    MkSerializedBytecode : (consts : Vect n PyConst) -> (proofs : Vect n (Elem x consts)) -> (bytecode : Vect m (PyBytecode consts)) -> PySerializedBytecode consts

addOneConst : PySerializedBytecode c1 -> (new_const : PyConst) -> PySerializedBytecode (new_const :: c1)
addOneConst (MkSerializedBytecode c1 proofs bytecode) new_const = MkSerializedBytecode ?ad ?cd ?ef

addToBytecode : PySerializedBytecode c1 -> (new_consts : Vect m PyConst) -> (new_bytecode : Vect m PyConst) -> PySerializedBytecode (c1 ++ new_consts)
addToBytecode (MkSerializedBytecode c1 proofs bytecode) [] new_bytecode = ?abcd_0
addToBytecode (MkSerializedBytecode c1 proofs bytecode) (x :: xs) new_bytecode = ?adasdasd

-- record PyCode where
--     constructor MkPyCode
--     variables : Vect n_var PyVarHandle
--     code : Vect n_code PyBytecode


-- 

data PyOperation : Type -> (consts_old : Vect n1 PyConst) -> (consts_new : Vect n2 PyConst) -> Type where
    -- PyCreateConst : (value : PyConst) -> PyOperation (PyVarHandle (value :: c1)) c1 (value :: c1)
    PyCreateConsts : (values : Vect n2 PyConst) -> PyOperation (Vect n2 (PyVarHandle values)) [] values
    PyReturn : (value : PyVarHandle c) -> PyOperation () c c
    (>>=) : PyOperation a c1 c2 -> (a -> PyOperation b c2 c2) -> PyOperation b c1 c2
    (>>) : PyOperation a c1 c2 -> PyOperation b c2 c3 -> PyOperation b c1 c3
    -- PyAssign : (value : PyVarHandle) -> PyOperation PyVarHandle c1 c1
    -- PyBinary : (v1 : PyData) -> (op : PyBinaryOp) -> (v2 : PyData) -> PyOperation PyVarHandle consts

-- mkconststr : (s : String) -> PyOperation (PyVarHandle (PyString s :: c1)) c1 (PyString s :: c1)
-- mkconststr s = PyCreateConst (PyString s)

compileProgram : {xs : Vect n PyConst} -> PyOperation a [] xs -> Vect n String
compileProgram {xs} _ = map (\c => case c of
                                        (PyString str) => str
                                        (PyInt i) => show i
                                        PyNone => "None"
                            ) xs


createVarHandles : (xy : Vect n PyConst) -> Vect n (PyVarHandle xy)
createVarHandles [] = []
createVarHandles (x :: xs) = (MkPyVarHandle x Here :: (map (\(MkPyVarHandle y ys) => MkPyVarHandle y (There ys)) (createVarHandles xs)))

turnToBytecode : (consts : Vect n PyConst) -> PyOperation a xs xy -> (a, List (PyBytecode xy))
turnToBytecode consts (PyCreateConsts xy) = (createVarHandles xy, [])
turnToBytecode consts (PyReturn value) = ((), [LOAD_CONST value])
turnToBytecode consts (x >>= f) = let (a', code) = turnToBytecode consts x in turnToBytecode consts (f a')
turnToBytecode consts (x >> y) = let (a', code) = turnToBytecode consts x in turnToBytecode consts y

compile : {n : _} -> {xs : Vect n PyConst} -> PyOperation () [] xs -> List (PyBytecode xs)
compile {xs} x = let (a, b) = turnToBytecode xs x in [RESUME] ++ b ++ [RETURN]

compiled = compile       $  do consts <- PyCreateConsts [
                                                PyString "sveikas",
                                                PyString "pasauli"
                                            ]
                               PyReturn (index 1 consts)


-- testProg : {xs : Vect _ _} -> PyOperation () [] xs
-- testProg {xs} = do PyStart
--                    var1 <- mkconststr "sveikas"
--                    var2 <- mkconststr "pasauli"
--                    PyReturn (PyVar var1)

-- tryGettingValue : PyData -> List PyConst
-- tryGettingValue (PyConstData x) = [x]
-- tryGettingValue (PyVar x) = []

-- parseConsts : PyOperation a -> List PyConst -> List PyConst
-- parseConsts (PyAssign value) xs = tryGettingValue value :: xs
-- parseConsts (PyBinary v1 op v2) xs = ?parseConsts_rhs_1
-- parseConsts (PyReturn value) xs = ?parseConsts_rhs_2
-- parseConsts (x >>= f) xs = ?parseConsts_rhs_3
-- parseConsts (x >> y) xs = ?parseConsts_rhs_4

-- compile : PyOperation () -> PyCode
-- compile op = let consts = parseConsts op
--              in MkPyCode [] []
-- 

