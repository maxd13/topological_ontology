import math.alexandroff_space math.notation
open set topological_space classical
set_option pp.generalized_field_notation true
local attribute [instance] prop_decidable
noncomputable theory
universes u v

-- THIS FILE IS A WORK IN PROGRESS

/-- An **equilogical space** is a `T₀`-space and a setoid. -/
structure equispace (α : Type*) extends topological_space α, setoid α := 
  [t₀ : @t0_space α to_topological_space]


attribute [class] equispace
variable {α : Type*}
instance equi_top  [E : equispace α]  : topological_space α := E.to_topological_space
instance equi_setoid  [E : equispace α]  : setoid α := E.to_setoid
instance equi_t0  [E : equispace α]  : t0_space α := E.t₀


/-- An **equimorphism** is a continuous map between 
    equilogical spaces which preserves the setoid structure. -/
structure equimorphism (α : Type u) (β : Type v) [E₁ : equispace α] [E₂ : equispace β] :=
  (map : α → β)
  (continuous : continuous map)
  (homo : ∀ x y : α, x ≈ y → map x ≈ map y)

#check @prod

