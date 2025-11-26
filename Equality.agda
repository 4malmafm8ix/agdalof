module Equality where

infix  4 _==_

data _==_ : {A : Set} -> A -> A -> Set where
        refl : {A : Set} -> {x : A} -> x == x

-- Equality is an equivalence relation.
symm : {A : Set} -> {x y : A} -> 
        x == y -> y == x
symm refl = refl

trans : {A : Set} -> {x y z : A} -> 
        x == y -> y == z -> x == z
trans refl refl = refl

-- Substitute equals for equals in functions.
cong1 : {A B : Set} -> {a b : A} ->
        (f : A -> B) -> a == b -> f a == f b 
cong1 f refl = refl 

-- Leibniz "Two things are equal if 
--          they have the same properties"
subst : {A : Set} -> (C : A -> Set) ->
        {x y : A} -> x == y -> C x -> C y
subst C refl hyp-cx = hyp-cx

{-
We need some syntactic sugar for equational 
reasoning so that we don't reply on many 
applications of trans, symm etc. 

For this we follow Wadler from PLFiA
-}

infix  1 equational_
infixr 2 _==⟨_⟩_ _==⟨⟩_
infix  3 _qed

-- Start calculation with equational:
equational_ : {A : Set} -> {x y : A} → x == y → x == y
equational x==y = x==y

-- Standard step with justification
_==⟨_⟩_ : {A : Set} -> (x : A)-> {y z : A} → x == y → y == z → x == z
_==⟨_⟩_ x x==y y==z = trans x==y y==z

-- Step with no justification (definitional equality)
_==⟨⟩_ : {A : Set} -> (x : A) -> {y : A} → x == y → x == y
_==⟨⟩_ x x==y = x==y

_qed : {A : Set} -> (x : A) → x == x
x qed = refl

