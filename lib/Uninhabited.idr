module Uninhabited

class Uninhabited t where
  total uninhabited : t -> _|_

instance Uninhabited (Fin Z) where
  uninhabited Z impossible
  uninhabited (S f) impossible

instance Uninhabited (Nat.Z = Nat.S n) where
  uninhabited refl impossible

