import metaphysics.metaphysics states
open set topological_space classical
local attribute [instance] prop_decidable

namespace ontology


section theism
  
  variable (ω : ontology)

  -- theism is the doctrine that the necessary being is simple.
  def theism (ω : ontology) := ω.nb.simple
        
  -- strong Platonism is logically equivalent to theism
  lemma splatonism_iff_theism :  ω.splatonism ↔ ω.theism := sorry


  -- Classical Theism is an extension of theism which 
  -- furthermore claims that there is a possible world 
  -- in which the necessary being exists alone.
  def ctheism := ∃ (w : ω.world), w.entities = {ω.nb.val}

  -- this is a not so trivial proof that if the nb exists alone,
  -- then it has no accidents, because accidents are contingent.
  @[simp] theorem theism_of_ctheism : ω.ctheism → ω.theism := sorry

  -- greek theism is non-classical theism
  def greek_theism := ω.theism ∧ ¬ ω.ctheism

end theism

section divine_substances

  variables {ω : ontology} (s : ω.substance)

  -- A substance is purely actual if it has no passive potency
  -- to be different from what it is, i.e. if it has a single state.
  def substance.purely_actual := ∀ w₁ w₂ : ω.world, s.state w₁ = s.state w₂
  
  -- Only the necessary being can be purely actual, 
  -- in which case theism follows.
  def eq_nb_of_purely_actual : s.purely_actual → s = ω.nb :=
  begin
      intros h,
      simp [substance.purely_actual] at h,
      ext,
      simp [nb, nbe],
      obtain ⟨y, hy⟩ := s.val.ne,
      specialize h x y,
      replace hy := exists_iff_in_state.mp hy,
      rw ←h at hy,
      exact exists_iff_in_state.2 hy,
  end

  
  theorem simple_of_purely_actual : s.purely_actual → s.simple  := sorry

end divine_substances

end ontology