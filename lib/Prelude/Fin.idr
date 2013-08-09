module Prelude.Fin

import Prelude.Nat
import Prelude.Either

data Fin : Nat -> Type where
    Z : Fin (S k)
    S : Fin k -> Fin (S k)

instance Eq (Fin n) where
    (==) Z Z = True
    (==) (S k) (S k') = k == k'
    (==) _ _ = False

finToNat : Fin n -> Nat -> Nat
finToNat Z a = a
finToNat (S x) a = finToNat x (S a)

instance Cast (Fin n) Nat where
    cast x = finToNat x Z

finToInt : Fin n -> Integer -> Integer
finToInt Z a = a
finToInt (S x) a = finToInt x (a + 1)

instance Cast (Fin n) Integer where
    cast x = finToInt x 0

weaken : Fin n -> Fin (S n)
weaken Z     = Z
weaken (S k) = S (weaken k)

strengthen : Fin (S n) -> Either (Fin (S n)) (Fin n)
strengthen {n = S k} Z = Right Z
strengthen {n = S k} (S i) with (strengthen i)
  strengthen (S k) | Left x   = Left (S x)
  strengthen (S k) | Right x  = Right (S x)
strengthen f = Left f

last : Fin (S n)
last {n=Z} = Z
last {n=S _} = S last

total fSinjective : {f : Fin n} -> {f' : Fin n} -> (S f = S f') -> f = f'
fSinjective refl = refl


-- Construct a Fin from an integer literal which must fit in the given Fin

natToFin : Nat -> (n : Nat) -> Maybe (Fin n)
natToFin Z     (S j) = Just Z
natToFin (S k) (S j) with (natToFin k j)
                          | Just k' = Just (S k')
                          | Nothing = Nothing
natToFin _ _ = Nothing

integerToFin : Integer -> (n : Nat) -> Maybe (Fin n)
integerToFin x = natToFin (cast x)

data IsJust : Maybe a -> Type where
     ItIsJust : IsJust {a} (Just x) 

fromInteger : (x : Integer) -> 
        {default (ItIsJust _ _) 
             prf : (IsJust (integerToFin x n))} -> Fin n
fromInteger {n} x {prf} with (integerToFin x n)
  fromInteger {n} x {prf = ItIsJust} | Just y = y

