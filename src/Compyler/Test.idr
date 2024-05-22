module Compyler.Test

import Data.Vect

data PyData = PyString String | PyInt Bits32 | PyNone
data PyConst = MkPyConst String PyData

data ElemInConsts : String -> Vect n PyConst -> Type where
  MkHere : ElemInConsts x ((MkPyConst x d) :: xs)
  MkThere : ElemInConsts x xs -> ElemInConsts x (x :: xs)

-- data ElemInConsts : String -> Vect n PyConst -> Type where
--   MkHere : ElemInConsts x (MkPyConst x data :: xs)
--   MkThere : ElemInConsts x xs -> ElemInConsts x (y :: xs)

