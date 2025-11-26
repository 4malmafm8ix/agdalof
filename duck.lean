/-

File        :: studyDuck
Author      :: Robert Culling
Description :: Studying inductive definitions and recursors.

In this file we see how inductive types can be used to
define the logical connectives ∧ ∨ ∃ and ⊥ ⊤

Note: the connectives → ∀ ¬ each come from the dependent
arrow type. This means inductive definitions and dependent
arrows are enough to define all connectives of first order logic.

What remains are to define predicates. Like equality...
But these too can be defined inductively!

These are my notes from studying Chapter 7 of Theorem Proving
in Lean 4.

-/
namespace studyDuck

inductive Bot : Prop

#print Bot.rec

-- No constructors => nothing to account for when eliminating!
noncomputable def Bot.elim {α : Type u} (x : Bot) : α :=
  Bot.rec (motive := fun _ => α) x

inductive Top : Prop where
  | duh : Top

#print Top.rec

noncomputable def TopNat (x : Top) : Nat :=
  Top.rec (motive := fun _ => Nat) 888000999 x

-- Bot can map to any type.
-- Top can map to any inhabited type.

-- Products and Conjunction as inductive types.
inductive Product (α : Type u) (β : Type v) where
  | mk : α → β → Product α β

#check Product.rec

noncomputable def first {α : Type u} {β : Type v} (t : Product α β) : α :=
  Product.rec (motive := fun (_ : Product α β) => α) (fun (a : α) (_ : β) => a) t

noncomputable def second {α : Type u} {β : Type v} (t : Product α β) : β :=
  Product.rec (fun (_ : α) (b : β) => b) t

noncomputable def prod_comm {α : Type u} {β : Type v} (t : Product α β) :
  Product β α :=
    Product.mk (second t) (first t)

inductive And (α β : Prop) : Prop where
  | intro : α → β → And α β

def And.elim_l {α : Prop} {β : Prop} (t : And α β) : α :=
  And.rec (fun (a : α) _ => a) t

def And.elim_r {α : Prop} {β : Prop} (t : And α β) : β :=
  And.rec (fun _ (b : β) => b) t

def And_comm {α : Prop} {β : Prop} (t : And α β) :
  And β α := And.intro (And.elim_r t) (And.elim_l t)

-- Sum and Disjunction as inductive types.
inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : β → Sum α β

#print Sum.rec

noncomputable def Sum.elim {α : Type u} {β : Type v} {γ : Type w}
  (t : Sum α β) (f : α → γ) (g : β → γ) : γ :=
    Sum.rec (motive := fun _ => γ) f g t

inductive Or (α : Prop) (β : Prop) : Prop where
  | intro_l : α → Or α β
  | intro_r : β → Or α β

noncomputable def Or.elim {α β γ : Prop}
  (t : Or α β) (f : α → γ) (g : β → γ) : γ :=
    Or.rec (motive := fun _ => γ) f g t

-- Dependent product and Existential quantifier
inductive Sigma {α : Type u} (P : α → Type v) where
  | mk : (a : α) → P a -> Sigma P

#print Sigma.rec

noncomputable def Sigma.elim {α : Type u} {P : α → Type v} {γ : Type w}
  (t : Sigma P) (f : (a : α) → P a → γ) : γ :=
    Sigma.rec (motive := fun _ => γ) f t

inductive Exists {α : Type u} (P : α → Prop) : Prop where
  | intro : (a : α) → P a → Exists P

#print Exists.rec

def Exists.elim {α : Type u} {P : α → Prop} {γ : Prop}
  (t : Exists P) (f : (a : α) → P a → γ) : γ :=
    Exists.rec (motive := fun _ => γ) f t


end studyDuck
