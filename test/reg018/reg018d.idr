module Main

total
pull : Fin (S n) -> Vect (S n) a -> (a, Vect n a)
pull {n=Z}   _      (x :: xs) = (x, xs)
-- pull {n=S q} Z     (Vect.(::) {n=S _} x xs) = (x, xs)
pull {n=S _} (S n) (x :: xs) =
  let (v, vs) = pull n xs in
        (v, x::vs)

main : IO ()
main = print (pull Z [0, 1, 2])
