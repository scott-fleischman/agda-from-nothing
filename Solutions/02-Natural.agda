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
2+2 = equal

2+2≢5 : 2 + 2 ≢ 5
2+2≢5 ()

1+1≢3 : 1 + 1 ≢ 3
1+1≢3 ()

2^3 : 2 ^ 3 ≡ 8
2^3 = equal

2^8 : 2 ^ 8 ≡ 256
2^8 = equal

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
x+0 (suc x) = congruence suc (x+0 x) -- Goal: suc x + 0 ≡ suc x

x*1 : (x : Natural) → x * 1 ≡ x
x*1 zero = equal
x*1 (suc x) rewrite x*1 x = equal

1*x : (x : Natural) → 1 * x ≡ x
1*x zero = equal
1*x (suc x) rewrite 1*x x = equal

+-associative : (x y z : Natural) → (x + y) + z ≡ x + (y + z)
+-associative zero y z = equal
+-associative (suc x) y z rewrite +-associative x y z = equal

+-suc : (x y : Natural) → x + suc y ≡ suc (x + y)
+-suc zero y = equal
+-suc (suc x) y rewrite +-suc x y = equal

+-commutative : (x y : Natural) → x + y ≡ y + x
+-commutative zero y rewrite x+0 y = equal
+-commutative (suc x) y
  rewrite +-suc y x
  | +-commutative x y
  = equal

+*-dist : (x y z : Natural) → (x + y) * z ≡ (x * z) + (y * z)
+*-dist zero y z = equal
+*-dist (suc x) y z
  rewrite +-associative z (x * z) (y * z)
  | +*-dist x y z
  = equal

*-associative : (x y z : Natural) → (x * y) * z ≡ x * (y * z)
*-associative zero y z = equal
*-associative (suc x) y z
  rewrite +*-dist y (x * y) z
  | *-associative x y z
  = equal

*-suc : (x y : Natural) → x * suc y ≡ x + (x * y)
*-suc zero y = equal
*-suc (suc x) y
  rewrite *-suc x y
  | symmetry (+-associative y x (x * y))
  | symmetry (+-associative x y (x * y))
  | +-commutative x y
  = equal

*-commutative : (x y : Natural) → x * y ≡ y * x
*-commutative zero y rewrite x*0 y = equal
*-commutative (suc x) y
  rewrite *-suc y x
  | *-commutative x y
  = equal

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
transitivity .0 .0 z (zero≤ .0) (zero≤ .z) = zero≤ z
transitivity .0 .(suc x) .(suc y) (zero≤ .(suc x)) (suc≤suc x y right) = zero≤ (suc y)
transitivity .(suc x) .(suc y) .(suc z) (suc≤suc x y left) (suc≤suc .y z right) = suc≤suc x z (transitivity x y z left right)

open import 01-Boolean using (Boolean; true; false)

_≤?_ : Natural → Natural → Boolean
zero ≤? y = true
suc x ≤? zero = false
suc x ≤? suc y = x ≤? y

2≤?3 : 2 ≤? 3 ≡ true
2≤?3 = equal

3≤?2 : 3 ≤? 2 ≡ false
3≤?2 = equal

equal≤? : (x y : Natural) → x ≡ y → x ≤? y ≡ true
equal≤? zero .0 equal = equal
equal≤? (suc x) .(suc x) equal = equal≤? x x equal

antisymmetry-bool : (x y : Natural) → x ≤? y ≡ true → y ≤? x ≡ true → x ≡ y
antisymmetry-bool zero zero equal equal = equal
antisymmetry-bool zero (suc y) equal ()
antisymmetry-bool (suc x) zero () right
antisymmetry-bool (suc x) (suc y) left right with antisymmetry-bool x y left right
antisymmetry-bool (suc x) (suc .x) left right | equal = equal 

data Total≤? (x y : Natural) : Set where
  x≤?y : x ≤? y ≡ true → Total≤? x y
  y≤?x : y ≤? x ≡ true → Total≤? x y

totality-bool : (x y : Natural) → Total≤? x y
totality-bool zero zero = x≤?y equal
totality-bool zero (suc y) = x≤?y equal
totality-bool (suc x) zero = y≤?x equal
totality-bool (suc x) (suc y) with totality-bool x y
totality-bool (suc x) (suc y) | x≤?y p = x≤?y p
totality-bool (suc x) (suc y) | y≤?x p = y≤?x p

transitivity-bool : (x y z : Natural) → x ≤? y ≡ true → y ≤? z ≡ true → x ≤? z ≡ true
transitivity-bool zero zero zero equal equal = equal
transitivity-bool zero zero (suc z) equal equal = equal
transitivity-bool zero (suc y) zero equal ()
transitivity-bool zero (suc y) (suc z) left right = equal
transitivity-bool (suc x) zero zero () right
transitivity-bool (suc x) zero (suc z) () right
transitivity-bool (suc x) (suc y) zero left ()
transitivity-bool (suc x) (suc y) (suc z) left right = transitivity-bool x y z left right
