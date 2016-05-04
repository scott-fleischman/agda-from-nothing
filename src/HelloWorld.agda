module HelloWorld where

open import Agda.Builtin.IO
open import Agda.Builtin.String
open import Agda.Builtin.Unit

postulate
  putStrLn : String → IO ⊤

-- NOTE: need to run `cabal install text` before compiling
{-# IMPORT Data.Text.IO #-}
{-# COMPILED putStrLn Data.Text.IO.putStrLn #-}

main : IO ⊤
main = putStrLn "Hello, world!"
