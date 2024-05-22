module Compyler.Effects

import Data.Vect

Effect : Type
Effect = (res : Type) -> (res’ : Type) -> (t : Type) -> Type

data EFFECT : Type where
    MkEff : Type -> Effect -> EFFECT

data EffElem : (Type -> Type -> Type -> Type) -> Type -> List EFFECT -> Type where
    Here : EffElem x a (MkEff a x :: es)
    There : EffElem x a es -> EffElem x a (y :: es)

-- updateResTy : {b : _} -> (es : List EFFECT) -> EffElem e a es -> e a b t -> List EFFECT
-- updateResTy {b} (MkEff a e :: es) Here n = (MkEff b e) :: es
-- updateResTy (x :: es) (There p) n = x :: updateResTy es p n

data SubList : List a -> List a -> Type where
    SubNil : SubList [] []
    Keep : SubList es fs -> SubList (x :: es) (x :: fs)
    Drop : SubList es fs -> SubList es (x :: fs)

updateWith : (fs’ : List a) -> (es : List a) -> SubList fs es -> List a
updateWith (y :: fs) (x :: es) (Keep rest) = y :: updateWith fs es rest
updateWith fs (x :: es) (Drop rest) = x :: updateWith fs es rest
updateWith [] [] SubNil = []

(:::) : lbl -> EFFECT -> EFFECT

interface Handler (e : Effect) where
    handle : res -> (eff : e res res’ t) -> (res’ -> t -> a) -> a

-- data Env : (Vect n EFFECT) -> Type where
--     Nil : Env Nil
--     (::) : Handler eff => a -> Env es -> Env (MkEff a eff :: es)

data Env : (a : Vect n EFFECT) -> Type where
    MkEnv : xs -> Env a

data EffM : Type -> (Vect n1 EFFECT) -> (Vect n2 EFFECT) -> Type where
    Return : a -> EffM a es es
    (>>=) : EffM a c1 c2 -> (a -> EffM b c2 c3) -> EffM b c1 c3

effInt : Env c1 -> EffM b c1 c2 -> (Env c2 -> b -> c) -> c
effInt env (Return x) k = k env x
effInt env (prog >>= c) k = effInt env prog (\env’, p’ => effInt env’ (c p’) k)
-- effInt x (MkEffectP prf eff) f = ?effInt_rhs_2
-- effInt x (LiftP prf y) f = ?effInt_rhs_3

-- effInt env (MkEffectP prf effP) k = execEff env prf effP k
-- effInt env (LiftP prf effP) k = let env’ = dropEnv env prf in effInt env’ effP (\envk, p’ => k (rebuildEnv envk prf env) p’)
-- effInt env ((:-) l prog) k = let env’ = unlabel env in effInt env’ prog (\envk, p’ => k (relabel l envk) p’)
