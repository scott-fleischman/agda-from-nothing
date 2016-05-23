module 03-Equality where

open import Agda.Primitive using (Level)

data _≡_ {a : Level} {A : Set a} (x : A) : A → Set a where
  equal : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL equal #-}

symmetry
  : {a : Level}
  → {A : Set a}
  → (x y : A)
  → x ≡ y
  → y ≡ x
symmetry x .x equal = equal

transitivity
  : {a : Level}
  → {A : Set a}
  → (x y z : A)
  → x ≡ y
  → y ≡ z
  → x ≡ z
transitivity x y z left right = {!!}

congruence
  : {a b : Level}
  → {A : Set a} {B : Set b}
  → (f : A → B)
  → (x y : A)
  → x ≡ y
  → f x ≡ f y
congruence f x y p = {!!}

transport
  : {a b : Level}
  → {A : Set a}
  → (x y : A)
  → (P : A → Set b)
  → x ≡ y
  → P x
  → P y
transport x y P p px = {!!}
