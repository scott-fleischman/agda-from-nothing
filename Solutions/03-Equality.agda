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
transitivity x .x .x equal equal = equal

congruence
  : {a b : Level}
  → {A : Set a} {B : Set b}
  → (f : A → B)
  → (x y : A)
  → x ≡ y
  → f x ≡ f y
congruence f x .x equal = equal

transport
  : {a b : Level}
  → {A : Set a}
  → (x y : A)
  → (P : A → Set b)
  → x ≡ y
  → P x
  → P y
transport x .x P equal px = px

leibniz
  : {a : Level}
  → {A : Set a}
  → (x y : A)
  → ((P : A → Set a) → P x → P y)
  → x ≡ y
leibniz x y H = H (x ≡_) equal
