module Compyler.Compyler

%default total

data PyVarHandle = PyVarName String
data PyBinaryOp = Add | Subtract | Multiply | Divide
data PyData = PyString String | PyInt Integer | PyNone | PyVar PyVarHandle

data PyOperation : Type -> Type where
    PyAssign : (value : PyData) -> PyOperation PyVarHandle
    PyBinary : (v1 : PyData) -> (op : PyBinaryOp) -> (v2 : PyData) -> PyOperation PyVarHandle
    PyReturn : (value : PyData) -> PyOperation ()
    (>>=) : PyOperation a -> (a -> PyOperation b) -> PyOperation b
    (>>) : PyOperation a -> PyOperation b -> PyOperation b


testProg : PyOperation ()
testProg = do var1 <- PyAssign (PyString "sveikas")
              var2 <- PyAssign (PyString "pasauli")
              add_res <- PyBinary (PyVar var1) Add (PyVar var2)
              PyReturn (PyVar add_res)


