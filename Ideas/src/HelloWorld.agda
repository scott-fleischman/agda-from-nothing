{-# OPTIONS --no-termination-check #-}

module HelloWorld where

open import Agda.Builtin.IO
open import Agda.Builtin.String
open import Agda.Builtin.Unit

postulate
  putStrLn : String → IO ⊤
  _⟫=_  : {A B : Set} → IO A → (A → IO B) → IO B

{-# IMPORT Data.Text.IO #-}
{-# COMPILED putStrLn Data.Text.IO.putStrLn #-}
{-# COMPILED _⟫=_ (\ _ _ a f -> a >>= f) #-}

main : IO ⊤
main
  = putStrLn "Hello, world!"
  ⟫= λ _ → main
