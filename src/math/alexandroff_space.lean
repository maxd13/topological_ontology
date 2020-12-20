import topology.bases
       topology.order 
       topology.homeomorph
       topology.subset_properties
       topology.instances.real
       data.fintype.basic
       tactic.tidy
universe u
open set classical tactic
local attribute [instance] prop_decidable

-- Module used for defining auxiliary mathematics needed for ontology.

namespace topological_space

/-- An Alexandroff, or Alexandroff-discrete, space is a topological space
  in which arbitrary intersections of open sets are open. -/
class alexandroff_space (α : Type u) [t : topological_space α] : Prop :=
  (alexandroff : ∀ {I} (f : I → set α), (∀ i, t.is_open (f i)) → t.is_open ⋂ i, f i)

variables {α : Type u} (t : topological_space α)
variables (x y : α) 
include t

def specialization : Prop :=
  ∀ s, t.is_open s → x ∈ s → y ∈ s 


instance specialization_order [h : t0_space α] : partial_order α := 
{ le := t.specialization,
  le_refl := by simp [specialization],
  le_trans := by finish [specialization],
  le_antisymm := begin
    intros a b h₁ h₂,
    replace h := h.t0,
    specialize h a b,
    simp [specialization] at *,
    by_contradiction hyp,
    specialize h hyp,
    obtain ⟨u, hu, ⟨h₃,h₄⟩|⟨h₃,h₄⟩⟩ := h;
    specialize h₁ u hu;
    specialize h₂ u hu;
    finish,
  end 
}

omit t

end topological_space

def uncountable (α : Type u) := infinite α ∧ ¬ nonempty (α ≃ ℕ)