import topology.bases
       topology.order 
       topology.homeomorph
       topology.subset_properties
       topology.instances.real
       topology.constructions
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
include t

def specialization (x y : α) : Prop :=
  ∀ s, t.is_open s → x ∈ s → y ∈ s 

@[priority std.priority.default - 100]
instance specialization_order [h : @t0_space α t] : partial_order α := 
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

instance sierpinski_t0 : @t0_space Prop sierpinski_space :=
  begin
    constructor,
    intros p q h,
    use {true}, simp [is_open],
    cases prop_complete p with hp hp;
    cases prop_complete q with hq hq;
    simp [hp, hq, xor];
    simp [hp, hq] at h;
    contradiction,
  end

def upper₀ [partial_order α] (s : set α) : Prop := 
  ∀ x y : α, x ≤ y → x ∈ s → y ∈ s

def alexandroff₀_of : partial_order α → topological_space α :=
  assume order, 
  { is_open := @upper₀ α order,
  is_open_univ := by simp [upper₀],
  is_open_inter := 
  begin
    intros s₁ s₂ h₁ h₂,
    simp [upper₀] at *,
    intros x y h₃ h₄ h₅, 
    constructor,
      apply h₁ x y; assumption,
    apply h₂ x y; assumption,
  end,
  is_open_sUnion :=
  begin
    intros S h,
    simp [upper₀],
    intros x y h₁ s h₂ h₃,
    refine ⟨s, h₂, _⟩,
    specialize h s h₂, simp [upper₀] at h,
    apply h; assumption,
  end }

instance alexandroff₀_t0  (order) : @t0_space α (alexandroff₀_of order) :=
  let le := @partial_order.le _ order,
      upper := @upper₀ _ order
  in
  begin
    constructor,
    intros x y h₀,
    by_cases h : le x y,
      use {w | le y w},
      constructor,
        change (upper {w : α | le y w}), 
        simp [upper, upper₀],
        intros a b h₁ h₂,
        apply @partial_order.le_trans _ order y; 
        assumption,
      have c : le y y := @partial_order.le_refl _ order y,
      simp [xor],
      change (le y x ∧ ¬le y y ∨ le y y ∧ ¬le y x),
      simp [c],
      intros insanity,
      have c := @le_antisymm _ order x y h insanity,
      contradiction,
    use {w | le x w},
    constructor,
      change (upper {w : α | le x w}),
      simp [upper, upper₀],
      intros a b h₁ h₂,
      apply @partial_order.le_trans _ order x; 
      assumption,
    have c : le x x := @partial_order.le_refl _ order x,
    simp [xor],
    change (le x x ∧ ¬le x y ∨ le x y ∧ ¬le x x),
    simpa [c],
  end

end topological_space

def uncountable (α : Type u) := infinite α ∧ ¬ nonempty (α ≃ ℕ)