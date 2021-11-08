import order.lattice

-- Module used solely for defining notation classes

class has_box (α : Type*) :=
  (box : α → Prop)

-- may change binding power in the future, depending on necessity
-- currently has the same power as logical negation
prefix `□`:100  := has_box.box

class has_black_box (α : Type*) :=
  (box : α → α)

-- may change binding power in the future, depending on necessity
-- currently has the same power as logical negation
prefix `◾`:100  := has_black_box.box

class has_diamond (α : Type*) :=
  (diamond : α → Prop)

prefix `⋄`:100  := has_diamond.diamond

class has_black_diamond (α : Type*) :=
  (diamond : α → α)

prefix `✦`:100  := has_black_diamond.diamond

reserve prefix `~`:100
class has_tilde (α : Type*) :=
  (tilde : α → α)

prefix `~` := has_tilde.tilde

class has_entailment (α : Type*) (β := α) :=
  (entails : α → β → Prop)

infixr ` ⇒ ` := has_entailment.entails

def strict_entailment {α} [has_entailment α] (x y : α) := x ⇒ y ∧ ¬ (y ⇒ x)
def negation_entailment {α} [has_entailment α] (x y : α) := ¬ (x ⇒ y)
def equivalence_entailment {α} [has_entailment α] (x y : α) := x ⇒ y ∧ y ⇒ x
def comparable_entailment {α} [has_entailment α] (x y : α) := x ⇒ y ∨ y ⇒ x
def incomparable_entailment {α} [has_entailment α] (x y : α) := ¬ comparable_entailment x y
def inequivalence_entailment {α} [has_entailment α] (x y : α) := ¬ equivalence_entailment x y

infixr ` ⇒' `:50 := strict_entailment
infixr ` ⇏ `:50 := negation_entailment
infixr ` ⇔ `:50 := equivalence_entailment
infixr ` ⇎ `:50 := inequivalence_entailment
infixr ` ≡ ` := comparable_entailment
infixr ` ≢ `:50 := incomparable_entailment


instance cross_entailment₁ (α β γ : Type*) [has_entailment β] 
                          [c₁ : has_coe α β] [c₂ : has_coe γ β]
                          : has_entailment α γ := ⟨λ x y, (@has_coe.coe _ _ c₁ x) ⇒ (@has_coe.coe _ _ c₂ y)⟩

instance cross_entailment₂ (α β : Type*) [has_entailment β] 
                          [c : has_coe α β]
                          : has_entailment α β := ⟨λ x y, (@has_coe.coe _ _ c x) ⇒ y⟩

instance cross_entailment₃ (α β : Type*) [has_entailment β] 
                          [c : has_coe α β]
                          : has_entailment β α := ⟨λ x y, x ⇒ (@has_coe.coe _ _ c y)⟩

instance cross_entailment₄ (α β : Type*) [has_entailment β] 
                          [c : has_coe α β]
                          : has_entailment α α := ⟨λ x y, (@has_coe.coe _ _ c x) ⇒ (@has_coe.coe _ _ c y)⟩

class has_local_entailment (α : Type*) :=
  (entails : α → α → α)

reserve infixr ` ⟶ `:50
infixr ` ⟶ ` := has_local_entailment.entails

def local_neg {α : Type*} [has_local_entailment α] [has_neg α] (x y : α) := -( x ⟶ y)

infixr ` !⟶ `:50 := local_neg

def local_eq {α : Type*} [has_local_entailment α] [has_inf α] (x y : α) := (x ⟶ y) ⊓ (y ⟶ x) 

infixr ` ⟷ `:50 := local_eq

def local_neq {α : Type*} [has_local_entailment α] [has_inf α] [has_neg α] (x y : α) := -(x ⟷ y)

infixr ` !⟷ `:50 := local_neq 