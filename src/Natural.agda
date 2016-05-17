{-# OPTIONS --exact-split #-}

module Natural where

data Natural : Set where
  zero : Natural
  suc : Natural → Natural
{-# BUILTIN NATURAL Natural #-}

_+_ : Natural → Natural → Natural
zero + y = y
(suc x) + y = suc (x + y)
{-# BUILTIN NATPLUS _+_ #-}

_-_ : Natural → Natural → Natural
x - zero = x
zero - suc y = zero
suc x - suc y = x - y
{-# BUILTIN NATMINUS _-_ #-}

_*_ : Natural → Natural → Natural
zero * y = zero
suc x * y = y + (x * y)
{-# BUILTIN NATTIMES _*_ #-}

_^_ : Natural → Natural → Natural
x ^ zero = suc zero
x ^ suc y = x * (x ^ y)

open import Agda.Primitive
data _≡_ {ℓ : Level} {X : Set ℓ} (x : X) : X → Set ℓ where
  equal : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL equal #-}

infix 4 _+_
infix 3 _≡_ _≢_

data Empty : Set where

_≢_ : (x y : Natural) → Set
_≢_ x y = x ≡ y → Empty

0+0 : 0 + 0 ≡ 0
0+0 = equal

2+2 : 2 + 2 ≡ 4
2+2 = equal

2+2≢5 : 2 + 2 ≡ 5 → Empty
2+2≢5 ()

2^3 : 2 ^ 3 ≡ 8
2^3 = equal

2^8 : 2 ^ 8 ≡ 256
2^8 = equal

0+x : (x : Natural) → 0 + x ≡ x
0+x x = equal

congruence : {x y : Natural} → (f : Natural → Natural) → x ≡ y → f x ≡ f y
congruence f equal = equal

x+0 : (x : Natural) → x + 0 ≡ x
x+0 zero = equal -- Goal: zero + 0 ≡ zero

--x+0 (suc x) = congruence suc (x+0 x) -- Goal: suc x + 0 ≡ suc x

{-
x+0 (suc x) with x + 0 | x+0 x
--x+0 (suc x) | .x | equal = equal
x+0 (suc x) | r1 | r2 = x+0-aux x r1 r2
  where
  x+0-aux : (x r1 : Natural) → r1 ≡ x → suc r1 ≡ suc x
  x+0-aux x .x equal = equal
-}

x+0 (suc x) rewrite (x+0 x) = equal

0*x : ∀ x → 0 * x ≡ 0
0*x x = equal

x*0 : ∀ x → x * 0 ≡ 0
x*0 zero = equal
x*0 (suc x) = x*0 x

symmetry : ∀ {ℓ} → {X : Set ℓ} → {x y : X} → x ≡ y → y ≡ x
symmetry equal = equal

+-assoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
+-assoc zero y z = equal
--+-assoc (suc x) y z = congruence suc (+-assoc x y z)
+-assoc (suc x) y z rewrite +-assoc x y z = equal

+*-dist : ∀ x y z → (x + y) * z ≡ (x * z) + (y * z)
+*-dist zero y z = equal
+*-dist (suc x) y z
  rewrite symmetry (+-assoc z (x * z) (y * z))
  | +*-dist x y z
  = equal

*-assoc : ∀ x y z → x * (y * z) ≡ (x * y) * z
*-assoc zero y z = equal
*-assoc (suc x) y z
  rewrite +*-dist y (x * y) z
  | *-assoc x y z
  = equal
