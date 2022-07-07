import metaphysics.finitism
open set topological_space classical
set_option pp.generalized_field_notation true
local attribute [instance] prop_decidable
noncomputable theory

namespace ontology

-- WORK IN PROGRESS. WAS TRYING TO PROVE CONSISTENCY OF VIRTUAL FINITISM.
-- IT TURNS OUT TO BE INCONSISTENT. STILL CONCEPTS HERE MAY BE INTERESTING
-- IN THE FUTURE. SO FAR THEY DESCRIBE AN ONTOLOGICAL INTERPRETATION OF THE NATURAL NUMBERS.

namespace instances

  instance platonic_chain : topological_space ℕ := alexandroff₀_of infer_instance
  instance platonic_pyramid (layout : ℕ → ℕ := id) : topological_space (Σ n : ℕ, fin (layout n)) := sorry

  def Platonic_Chain : ontology := 
    { world := ℕ, t := instances.platonic_chain}

namespace Platonic_Chain
  def least : Platonic_Chain.entity → ℕ :=
    λ e, nat.find e.possible

  set_option pp.proofs true
  lemma entity_id : ∀ e : Platonic_Chain.entity, {k | nat.find e.possible ≤ k} = e.exists :=
    let upper := @upper₀ ℕ _ in
    begin
      intro e,
      ext n, constructor; intro h,
        simp at h,
        have c := e.existential,
        change (upper e.exists) at c,
        simp [upper, upper₀] at c,
        specialize c (nat.find e.possible) n,
        apply c h, clear c,
        exact nat.find_spec e.possible,
      apply nat.find_min'; assumption,
    end

  lemma least_inj : ∀ (n : ℕ), inj_on Platonic_Chain.least {e : Platonic_Chain.entity | e.exists n} :=
    begin
      intro n,
      simp [inj_on, least],
      intros x y h₁ h₂ h₃,
      rw ←(entity_id x),
      rw ←(entity_id y),
      rw h₃,
    end
    
  set_option pp.proofs false
  theorem ultrafin : Platonic_Chain.ultrafin :=
    begin
      simp [ultrafin, nbe, ext_iff, lsfinite],
      intro n, change (ℕ) at n,
      apply finite_of_finite_image (Platonic_Chain.least_inj n),
      suffices c : least '' {e : Platonic_Chain.entity | e.exists n} = {i | i ≤ n},
        rw c, exact finite_le_nat n,
      simp [least, image, ext_iff],
      intro m; constructor; intro h,
        obtain ⟨e, he₁, he₂⟩ := h,
        have c := nat.find_min' e.possible he₁, 
        rwa he₂ at c,
      let e : Platonic_Chain.entity,
        refine ⟨{k  : ℕ| m ≤ k}, _, ⟨m, _⟩⟩, swap,
          change (m ≤ m), exact nat.le_refl m,
        change (upper₀ {k : ℕ | m ≤ k}),
        simp [upper₀],
        intros x y h₁ h₂,
        exact le_trans h₂ h₁,
      refine ⟨e, by simpa [e], _⟩,
      apply le_antisymm,
        apply @nat.find_min' {k : ℕ | m ≤ k} _ e.possible m,
        change (m ≤ m), exact nat.le_refl m,
      exact nat.find_spec e.possible,
    end

end Platonic_Chain


end instances


end ontology