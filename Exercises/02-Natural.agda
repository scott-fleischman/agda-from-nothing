{-# OPTIONS --exact-split #-}

module 02-Natural where

infixl 6 _+_
infixl 7 _*_
infixl 4 _≡_ _≢_

data Natural : Set where
  zero : Natural
  suc : Natural → Natural
{-# BUILTIN NATURAL Natural #-}

_+_ : Natural → Natural → Natural
zero + y = y
(suc x) + y = suc (x + y)
{-# BUILTIN NATPLUS _+_ #-}

_-_ : Natural → Natural → Natural
x - y = {!!}

_*_ : Natural → Natural → Natural
zero * y = zero
suc x * y = y + (x * y)
{-# BUILTIN NATTIMES _*_ #-}

_^_ : Natural → Natural → Natural
x ^ y = {!!}

open import Agda.Primitive using (Level)
data _≡_ {ℓ : Level} {X : Set ℓ} (x : X) : X → Set ℓ where
  equal : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL equal #-}

data Empty : Set where

_≢_ : {ℓ : Level} → {X : Set ℓ} → (x y : X) → Set ℓ
x ≢ y = x ≡ y → Empty

0+0 : 0 + 0 ≡ 0
0+0 = equal

2+2 : 2 + 2 ≡ 4
2+2 = {!!}

2+2≢5 : 2 + 2 ≢ 5
2+2≢5 ()

1+1≢3 : 1 + 1 ≢ 3
1+1≢3 = {!!}

2^3 : 2 ^ 3 ≡ 8
2^3 = {!!}

2^8 : 2 ^ 8 ≡ 256
2^8 = {!!}

0*x : (x : Natural) → 0 * x ≡ 0
0*x x = equal

x*0 : (x : Natural) → x * 0 ≡ 0
x*0 zero = equal
x*0 (suc x) = x*0 x

symmetry
  : {x y : Natural}
  → x ≡ y
  → y ≡ x
symmetry equal = equal

congruence
  : {x y : Natural}
  → (f : Natural → Natural)
  → x ≡ y
  → f x ≡ f y
congruence f equal = equal

0+x : (x : Natural) → 0 + x ≡ x
0+x x = equal

x+0 : (x : Natural) → x + 0 ≡ x
x+0 zero = equal -- Goal: zero + 0 ≡ zero
x+0 (suc x) rewrite x+0 x = equal -- Goal: suc x + 0 ≡ suc x

x*1 : (x : Natural) → x * 1 ≡ x
x*1 x = {!!}

1*x : (x : Natural) → 1 * x ≡ x
1*x x = {!!}

+-associative : (x y z : Natural) → (x + y) + z ≡ x + (y + z)
+-associative zero y z = equal
+-associative (suc x) y z rewrite +-associative x y z = equal

+-suc : (x y : Natural) → x + suc y ≡ suc (x + y)
+-suc x y = {!!}

+-commutative : (x y : Natural) → x + y ≡ y + x
+-commutative zero y rewrite x+0 y = equal
+-commutative (suc x) y
  rewrite +-suc y x
  | +-commutative x y
  = equal

+*-dist : (x y z : Natural) → (x + y) * z ≡ (x * z) + (y * z)
+*-dist x y z = {!!}

*-associative : (x y z : Natural) → (x * y) * z ≡ x * (y * z)
*-associative x y z = {!!}

*-suc : (x y : Natural) → x * suc y ≡ x + (x * y)
*-suc zero y = equal
*-suc (suc x) y
  rewrite *-suc x y
  | symmetry (+-associative y x (x * y))
  | symmetry (+-associative x y (x * y))
  | +-commutative x y
  = equal

*-commutative : (x y : Natural) → x * y ≡ y * x
*-commutative x y = {!!}

data _≤_ : Natural → Natural → Set where
  zero≤ : (y : Natural) → zero ≤ y
  suc≤suc : (x y : Natural) → x ≤ y → suc x ≤ suc y

data Total≤ (x y : Natural) : Set where
  x≤y : x ≤ y → Total≤ x y
  y≤x : y ≤ x → Total≤ x y

totality : (x y : Natural) → Total≤ x y
totality zero y = x≤y (zero≤ y)
totality (suc x) zero = y≤x (zero≤ (suc x))
totality (suc x) (suc y) with totality x y
totality (suc x) (suc y) | x≤y p = x≤y (suc≤suc x y p)
totality (suc x) (suc y) | y≤x p = y≤x (suc≤suc y x p)

antisymmetry : (x y : Natural) → x ≤ y → y ≤ x → x ≡ y
antisymmetry .0 .0 (zero≤ .0) (zero≤ .0) = equal
antisymmetry .(suc x) .(suc y) (suc≤suc x y left) (suc≤suc .y .x right) rewrite antisymmetry x y left right = equal

transitivity : (x y z : Natural) → x ≤ y → y ≤ z → x ≤ z
transitivity x y z left right = {!!}

data Boolean : Set where
  true false : Boolean

_≤?_ : Natural → Natural → Boolean
x ≤? y = {!!}

2≤?3 : 2 ≤? 3 ≡ true
2≤?3 = {!!}

3≤?2 : 3 ≤? 2 ≡ false
3≤?2 = {!!}

equal≤? : (x y : Natural) → x ≡ y → x ≤? y ≡ true
equal≤? x y p = {!!}

antisymmetry-bool : (x y : Natural) → x ≤? y ≡ true → y ≤? x ≡ true → x ≡ y
antisymmetry-bool x y left right = {!!}

data Total≤? (x y : Natural) : Set where
  x≤?y : x ≤? y ≡ true → Total≤? x y
  y≤?x : y ≤? x ≡ true → Total≤? x y

totality-bool : (x y : Natural) → Total≤? x y
totality-bool x y = {!!}

transitivity-bool : (x y z : Natural) → x ≤? y ≡ true → y ≤? z ≡ true → x ≤? z ≡ true
transitivity-bool x y z left right = {!!}
