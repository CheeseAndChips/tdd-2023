module Lesson11
import Data.List
import Data.Nat
import Data.Fin
import Data.So
import Decidable.Equality

%default total

namespace Simple

        {- =================== Proof as in math books ==================
        |  THEOREM: B ⇒ A ⇒ (A ∧ B).
        |
        |  LEMMA 1: (B ∧ A) ⇒ (A ∧ B).
        |  Proof.
        |  Suffices assume (B ∧ A) and prove (A ∧ B) by "⇒-intro".
        |  From (B ∧ A) we have (A) by "∧-elim2".
        |  From (B ∧ A) we have (B) by "∧-elim1".
        |  From (A) and (B) we have (A ∧ B) by "∧-intro". □
        |
        |  Proof of the THEOREM.
        |  Suffinces assume (B) and prove (A ⇒ A ∧ B) by "⇒-intro".
        |  Next, suffices assume (A) and prove (A ∧ B) by "⇒-intro".
        |  From (B) and (A) we have (B ∧ A) by "∧-intro".
        |  From (B ∧ A) we have (A, B) by "LEMMA 1". □
        -}

        {- ============================== Formal: LEMMA 1 ==============================
        |  ------------------------------ (ax)          ------------------------------ (ax)
        |   (B ∧ A) ⊢ (B ∧ A), (A ∧ B)                (B ∧ A) ⊢ (B ∧ A), (A ∧ B)
        |  ------------------------------ (∧-elim)     ------------------------------- (∧-elim)
        |       (B ∧ A) ⊢ A, (A ∧ B)                       (B ∧ A) ⊢ B, (A ∧ B)
        |      --------------------------------------------------------------------- (∧-intro)
        |                          (B ∧ A) ⊢ (A ∧ B), (A ∧ B)
        |                         ------------------------------ (contr)
        |                               (B ∧ A) ⊢ (A ∧ B)
        |                            ------------------------ (⇒-intro)
        |                              ⊢ (B ∧ A) ⇒ (A ∧ B)
        |-}

        {- ============================== Formal: THEOREM ==============================
        |                                       ----------- (ax)   ----------- (ax)
        |                                        B, A ⊢ B           B, A ⊢ A
        |    ---------------------- (LEMMA 1)   ------------------------------ (∧-intro)
        |     ⊢ (B ∧ A) ⇒ (A ∧ B)                     B, A  ⊢ (B ∧ A)
        |    ------------------------------------------------------------ (⇒-elim)
        |                          B, A  ⊢ (A ∧ B)
        |                         ------------------ (⇒-intro)
        |                          B ⊢ A ⇒ (A ∧ B)
        |                        -------------------- (⇒-intro)
        |                         ⊢ B ⇒ A ⇒ (A ∧ B)
        |-}

        ||| We will have 2 proofs of the same type.
        pair_t : {a: Type} -> {b : Type} -> Type
        pair_t = (b -> a -> (a, b))

        ||| The initial proof.
        pair_2 : pair_t {a} {b}
        pair_2 y x = (\z => ((snd z), (fst z))) (y, x) -- note, inverted

        ||| Evaluate the "apply".
        pair_2' : pair_t {a} {b}
        pair_2' y x = ((snd (y, x)), (fst (y, x)))

        ||| Evaluate the snd.
        pair_2'' : pair_t {a} {b}
        pair_2'' y x = (x, (fst (y, x)))

        ||| Evaluate the fst.
        pair_2''' : pair_t {a} {b}
        pair_2''' y x = (x, y)

        {- ========================= THEOREM (simplified) =========================
        |    ------------ (ax)     ----------- (ax)
        |      B, A ⊢ A             B, A ⊢ B
        |    ---------------------------------- (∧-intro)
        |             B, A ⊢ (A ∧ B)
        |          ------------------- (⇒-intro)
        |            B ⊢ A ⇒ (A ∧ B)
        |         ---------------------- (⇒-intro)
        |           ⊢ B ⇒ A ⇒ (A ∧ B)
        |-}

        {- =================== Proof as in math books ==================
        |  THEOREM: B ⇒ A ⇒ (A ∧ B).
        |
        |  Proof of the THEOREM.
        |  Suffinces assume (B) and prove (A ⇒ A ∧ B) by "⇒-intro".
        |  Next, suffices assume (A) and prove (A ∧ B) by "⇒-intro".
        |  We have both (A) and (B), thus (A ∧ B) by "∧-intro". □
        -}

namespace PredicatesEtAl

    -- ∀ x ∈ X. P(x)  -- f : (x : Type) -> P(x)
    -- ∃ x ∈ X. P(x)  -- ( x : Type ** P(x) ) -- DPair

    -- ∀ a b : Nat. ∃ m : Nat. (m = a /\ m >= b) \/ (m = b /\ m >= a)

    mmax : Nat -> Nat -> Nat
    mmax k j = if k >= j then k else j

    mmax' : Nat -> Nat -> Nat
    mmax' k j = 0

    public export
    max'' : (a : Nat) -> (b : Nat) -> (m : Nat ** Either (m = a, GTE m b) (m = b, GTE m a))
    max'' 0 0 = (0 ** Left (Refl, LTEZero))
    max'' 0 (S k) = (S k ** Right (Refl, LTEZero))
    max'' (S k) 0 = (S k ** Left (Refl, LTEZero))
    max'' (S k) (S j) =
        case max'' k j of
            ((val ** (Left (xval, xprf)))) => (S val ** (Left ((cong S xval), LTESucc xprf)))
            ((val ** (Right (xval, xprf)))) => (S val ** Right ((cong S xval), LTESucc xprf))

    -- max''' : (a : Nat) -> (b : Nat) -> (m : Nat ** Either (m = a, GTE m b) (m = b, GTE m a))

namespace MaxAsPredicate

    data Max : (m : Nat) -> (a : Nat) -> (b : Nat) -> Type where
        Max0 : Max 0 0 0
        MaxA : Max (S a) (S a) 0
        MaxB : Max (S b) 0 (S b)
        MaxX : Max m a b -> Max (S m) (S a) (S b)

    max4 : (a : Nat) -> (b : Nat) -> (m : Nat ** Max m a b)
    max4 0 0 = (0 ** Max0)
    max4 0 (S k) = ((S k) ** MaxB)
    max4 (S k) 0 = ((S k) ** MaxA)
    max4 (S k) (S j) =
        let (val ** prf) = max4 k j in
        (S val ** MaxX prf)

namespace MaxAsSo
    fixDoubleNeg : {a : Bool} -> So (not (not a)) -> So a
    fixDoubleNeg {a=False} x impossible -- = ?aa -- x
    fixDoubleNeg {a=True} x = Oh

    invertCmp : {a : Nat} -> {b : Nat} -> So (compareNat a b == LT) -> So (compareNat b a == GT)
    invertCmp {a = 0} {b = 0} x = x
    invertCmp {a = 0} {b = (S k)} x = x
    invertCmp {a = (S k)} {b = 0} x = x
    invertCmp {a = (S k)} {b = (S j)} x = invertCmp x

    lol : (b : Nat) -> (a : Nat) -> So (not (not (compareNat a b == LT))) -> So (compareNat b a == GT)
    lol b a x = let fixed = fixDoubleNeg x
                in invertCmp fixed

    max5 : (a : Nat) -> (b : Nat) -> (m : Nat ** Either (m = a, So (m >= b)) (m = b, So (m > a)))
    max5 a b = case choose (a >= b) of
                    (Left x) => (a ** Left (Refl, x))
                    (Right x) => (b ** Right (Refl, lol b a x))

    data Maax : Type where
        Maa0 : Maax -> Maax
