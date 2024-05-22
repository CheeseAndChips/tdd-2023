module Compyler.EffectsFullImpl

Effect : Type
Effect = (res : Type) -> (res’ : Type) -> (t : Type) -> Type

data EFFECT : Type where
    MkEff : Type -> Effect -> EFFECT

data EffElem : (Type -> Type -> Type -> Type) -> Type -> List EFFECT -> Type where
    Here : EffElem x a (MkEff a x :: es)
    There : EffElem x a es -> EffElem x a (y :: es)

updateResTy : {b : _} -> (es : List EFFECT) -> EffElem e a es -> e a b t -> List EFFECT
updateResTy {b} (MkEff a e :: es) Here n = (MkEff b e) :: es
updateResTy (x :: es) (There p) n = x :: updateResTy es p n

data SubList : List a -> List a -> Type where
    SubNil : SubList [] []
    Keep : SubList es fs -> SubList (x :: es) (x :: fs)
    Drop : SubList es fs -> SubList es (x :: fs)

updateWith : (fs’ : List a) -> (es : List a) -> SubList fs es -> List a
updateWith (y :: fs) (x :: es) (Keep rest) = y :: updateWith fs es rest
updateWith fs (x :: es) (Drop rest) = x :: updateWith fs es rest
updateWith [] [] SubNil = []

(:::) : lbl -> EFFECT -> EFFECT

interface Handler (e : Effect) (m : Type -> Type) where
    handle : res -> (eff : e res res’ t) -> (res’ -> t -> m a) -> m a

data Env : (m : Type -> Type) -> List EFFECT -> Type where
    Nil : Env m Nil
    (::) : Handler eff m => a -> Env m es -> Env m (MkEff a eff :: es)

data EffM : (m : Type -> Type) -> List EFFECT -> List EFFECT -> Type -> Type where
    Return : a -> EffM m es es a
    (>>=) : EffM m es es’ a -> (a -> EffM m es’ es’’ b) -> EffM m es es’’ b
    MkEffectP : (prf : EffElem e a es) -> (eff : e a b t) -> EffM m es (updateResTy es prf eff) t
    LiftP : (prf : SubList fs es) -> EffM m fs fs’ t -> EffM m es (updateWith fs’ es prf) t

execEff : {e, m : _} -> Env m es -> (p : EffElem e res es) -> (eff : e res b a) -> (Env m (updateResTy es p eff) -> a -> m t) -> m t
execEff (val :: env) Here eff’ k = handle val eff’ (\res, v => k (res :: env) v)
execEff (val :: env) (There p) eff k = execEff env p eff (\env’, v => k (val :: env’) v)

effInt : {e : _} -> Env m es -> EffM m es es’ b -> (Env m es’ -> b -> m c) -> m c
effInt env (Return x) k = k env x
effInt env (prog >>= c) k = effInt env prog (\env’, p’ => effInt env’ (c p’) k)
effInt env (MkEffectP prf effP) k = execEff env prf effP k
effInt env (LiftP prf effP) k = let env’ = dropEnv env prf in effInt env’ effP (\envk, p’ => k (rebuildEnv envk prf env) p’)
-- effInt env ((:-) l prog) k = let env’ = unlabel env in effInt env’ prog (\envk, p’ => k (relabel l envk) p’)
