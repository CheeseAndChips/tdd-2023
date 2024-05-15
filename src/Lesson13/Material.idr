module Lesson13.Material

data MatState = Liquid | Gas | Solid
data MatStateTransition : (ty : Type) -> (pre : MatState) -> (ty -> MatState) -> Type where
    Melt : MatStateTransition () Solid (const Liquid)
    Freeze : MatStateTransition () Liquid (const Solid)
    Boil : MatStateTransition () Liquid (const Gas)
    Condense : MatStateTransition () Gas (const Liquid)
    (>>=) : MatStateTransition a s1 s2f -> ((res: a) -> MatStateTransition b (s2f res) s3f) -> MatStateTransition b s1 s3f
    (>>) : MatStateTransition a s1 (\_ => s2) -> MatStateTransition b s2 s3f -> MatStateTransition b s1 s3f

transition : MatStateTransition () Solid (const Solid)
transition = do Melt
                Boil
                Condense
                Freeze



