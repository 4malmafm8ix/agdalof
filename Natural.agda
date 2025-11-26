module Natural where

open import Equality
open import Logic

data ℕ : Set where 
    zero : ℕ 
    succ : ℕ -> ℕ

infixl 6 _+_    
infixl 7 _*_

_+_ : ℕ -> ℕ -> ℕ
_+_ zero m     = m
_+_ (succ n) m = succ (n + m)

_*_ : ℕ -> ℕ -> ℕ 
_*_ zero m     = zero
_*_ (succ n) m = (n * m) + m

PA1 : {x : ℕ} -> ¬ ((succ x) == zero)
PA1 ()

PA2 : {x y : ℕ} -> ((succ x) == (succ y)) -> x == y
PA2 refl = refl

PA3 : (x : ℕ) -> zero + x == x
PA3 _ = refl

PA4 : (x y : ℕ) -> (succ x) + y == succ (x + y)
PA4 _ _ = refl

PA5 : (x : ℕ) -> zero * x == zero
PA5 _ = refl 

PA6 : (x y : ℕ) -> (succ x) * y == (x * y) + y
PA6 _ _ = refl

add-zero : (x : ℕ) -> x + zero == x
add-zero zero     = refl
add-zero (succ x) = 
    equational 
        (succ x) + zero
    ==⟨⟩
        succ (x + zero)
    ==⟨ cong1 succ (add-zero x) ⟩
        succ x 
    qed

add-succ : (x y : ℕ) -> x + (succ y) == succ (x + y)
add-succ zero y     = refl 
add-succ (succ k) y =
    equational
        (succ k) + (succ y)
    ==⟨⟩
        succ (k + (succ y))
    ==⟨ cong1 succ (add-succ k y) ⟩
        succ (succ (k + y))
    ==⟨⟩
        succ ((succ k) + y) 
    qed

mul-zero : (x : ℕ) -> x * zero == zero
mul-zero zero     = refl
mul-zero (succ k) =
    equational
        (succ k) * zero
    ==⟨⟩
        (k * zero) + zero
    ==⟨ add-zero (k * zero) ⟩
        k * zero
    ==⟨ mul-zero k ⟩
        zero 
    qed

add-comm : (x y : ℕ) -> x + y == y + x
add-comm zero y     = symm (add-zero y)
add-comm (succ k) y =
    equational 
        (succ k) + y
    ==⟨⟩
        succ (k + y) 
    ==⟨ cong1 succ (add-comm k y) ⟩
        succ (y + k)
    ==⟨ symm (add-succ y k) ⟩
        y + (succ k)
    qed

add-assoc : (x y z : ℕ) -> (x + y) + z == x + (y + z)
add-assoc zero y z = refl
add-assoc (succ x) y z =
    equational
        ((succ x) + y) + z
    ==⟨⟩
        (succ (x + y)) + z
    ==⟨⟩
        succ ((x + y) + z)
    ==⟨ cong1 succ (add-assoc x y z) ⟩
        succ (x + (y + z))
    ==⟨⟩
        (succ x) + (y + z)
    qed