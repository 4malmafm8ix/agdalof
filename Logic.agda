module Logic where

data ⊤ : Set where
    <> : ⊤

-- Falsum introduction and elimination.
data ⊥ : Set where
    -- No constructors!

ex-falso : {A : Set} → ⊥ → A 
ex-falso () -- Case distinction on zero cases.

-- Conjunction introduction and elimination.
data _∧_ : Set → Set -> Set where
    _,_ : {A B : Set} -> A -> B -> A ∧ B

fst : {A B : Set} -> A ∧ B -> A
fst (a , _) = a

snd : {A B : Set} -> A ∧ B → B
snd (_ , b) = b

-- Disjunction introduction and elimination.
data _∨_ : Set → Set → Set where
    or-inl : {A B : Set} → A → A ∨ B
    or-inr : {A B : Set} → B → A ∨ B

or-elim : {A B C : Set} -> 
        A ∨ B → (A → C) → (B → C) → C
or-elim (or-inl a) f g = f a
or-elim (or-inr b) f g = g b

-- Negation is a function type.
¬ : Set -> Set 
¬ A = A → ⊥

-- Existential Quantifier Introduction and Elimination
data Exists : (A : Set) -> (P : A -> Set) -> Set where
    _,_ : {A : Set} -> {P : A -> Set} ->
                (a : A) -> P a -> Exists A P

∃ : {A : Set} -> (P : A -> Set) -> Set
∃ {A} P = Exists A P

exists-witness : {A : Set} -> {P : A -> Set} -> ∃ {A} P -> A
exists-witness (a , p) = a

exists-proof : {A : Set} -> {P : A -> Set} -> 
            (x : ∃ {A} P) -> P (exists-witness x)
exists-proof (a , p) = p

-- At this point we could actually define ∧ in terms of ∃.
Conjunction : (A : Set) -> (B : Set) -> Set
Conjunction A B = ∃ {A} (λ x -> B)


{-
    Agda's type system can encode logic in the form 
    of Gentzen; with rules of inference becoming 
    type constructors and destructors. As the Curry 
    Howard correspondence suggests. 

    What follows are a few theorems of propositional 
    logic with proofs given as programs!

    Pattern matching on inductive types in Agda make 
    these programs very easy and clean to write. 

-}

curry : {A B C : Set} -> (A ∧ B → C) -> (A → B → C)
curry f a b = f (a , b)

uncurry : {A B C : Set} -> (A → B → C) -> (A ∧ B → C)
uncurry f (a , b) = f a b

and-comm : {A B : Set} → A ∧ B → B ∧ A
and-comm (a , b) = (b , a)

or-comm : {A B : Set} -> A ∨ B -> B ∨ A 
or-comm (or-inl a) = or-inr a
or-comm (or-inr b) = or-inl b

composition : {A B C : Set} -> (A -> B) -> (B -> C) -> (A -> C)
composition f g a = g (f a)

or-map-disjuncts : {A B C D : Set} ->
                (A ∨ B) -> (A → C) -> (B -> D) -> (C ∨ D)
or-map-disjuncts (or-inl a) f g = or-inl (f a)
or-map-disjuncts (or-inr b) f g = or-inr (g b)

and-distrib-or : {A B C : Set} -> A ∧ (B ∨ C) -> (A ∧ B) ∨ (A ∧ C)
and-distrib-or (a , or-inl b) = or-inl (a , b) 
and-distrib-or (a , or-inr c) = or-inr (a , c)

and-factor-or : {A B C : Set} -> (A ∧ B) ∨ (A ∧ C) -> A ∧ (B ∨ C)
and-factor-or (or-inl (a , b)) = (a , or-inl b)
and-factor-or (or-inr (a , c)) = (a , or-inr c)

modus-tollens : {A B : Set} -> (A -> B) -> (¬ B) -> (¬ A)
modus-tollens = composition

double-negation-intro : {A : Set} -> A -> ¬ (¬ A)
double-negation-intro a f = f a

triple-negation-simplify : {A : Set} -> ¬ (¬ (¬ A)) -> ¬ A
triple-negation-simplify f a = f (double-negation-intro a)

not-factor-or : {A B : Set} -> (¬ A) ∨ (¬ B) -> ¬ (A ∧ B)
not-factor-or (or-inl na) (a , b) = na a  
not-factor-or (or-inr nb) (a , b) = nb b

not-factor-and : {A B : Set} -> (¬ A) ∧ (¬ B) -> ¬ (A ∨ B)
not-factor-and (na , nb) (or-inl a) = na a
not-factor-and (na , nb) (or-inr b) = nb b

not-distr-or : {A B : Set} -> ¬ (A ∨ B) -> (¬ A) ∧ (¬ B)
not-distr-or f = ((\a -> f (or-inl a)) , (\b -> f (or-inr b)))

disjunctive-syllogism : {A B : Set} -> (A ∨ B) -> (¬ A) -> B
disjunctive-syllogism (or-inl a) na = ex-falso (na a)
disjunctive-syllogism (or-inr b) na = b

cant-deny-lem : {A : Set} -> ¬ (¬ (A ∨ ¬ A))
cant-deny-lem f = f (or-inr (λ a -> f (or-inl a)))


