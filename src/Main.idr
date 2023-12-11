module Main

import Data.Vect

main : IO ()
main = do 
  putStrLn "Hello world"
  print (plus (S (S Z)) (S Z))

plus' : Nat -> Nat -> Nat
plus' Z  y = y
plus' (S n) y = S (plus' n y)

testVec : Vect 4 Int
testVec = 3 :: 4 :: 5 :: 6 :: Nil

data IsElem : a -> Vect n a -> Type where
  Here : {x:a} -> {xs:Vect n a} -> IsElem x (x :: xs)
  There : {x,y:a} -> {xs:Vect n a} -> IsElem x xs -> IsElem x (y :: xs)

inVect : IsElem 5 Main.testVec
inVect = There (There Here)
