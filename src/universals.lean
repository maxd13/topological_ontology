import states
       data.real.basic
       topology.instances.real
       measure_theory.borel_space
       measure_theory.measure_space
universe u
open set topological_space classical
local attribute [instance] prop_decidable

namespace ontology

  variables {ω : ontology}

  -- We can define virtual substances as products, 
  -- coproducts, subtypes and quotients of 
  -- state spaces of real substances.
  -- These spaces so generated represent the would be state spaces
  -- of entities which perhaps are not possible to exist.
  
  -- Concepts are virtual substances abstracted away from the state
  -- spaces of particulars substances. 
  -- Universals are concepts defined up to isomorphism.
  
  -- The process of abstraction, telling whether a Type has been
  -- abstracted away from particular substances.
  -- An element of this type is one possible way the topological
  -- space could be abstracted from the particulars, i.e.
  -- it is an abstraction of the space.
  class inductive abstraction (ω : ontology) : Π (α : Type u) [topological_space α], Type (u+1)
  | particular (s : ω.substance) : abstraction s.state
  | pi           {I : Type u} (get : I → Type u)
  [get_top : Π i : I, topological_space (get i)]
  (h : ∀ i : I, abstraction (get i) ) 
  : abstraction (Π i : I, (get i))
  
  | sigma        {I : Type u} (get : I → Type u)
  [get_top : Π i : I, topological_space (get i)]
  (h : ∀ i : I, abstraction (get i) ) 
  : abstraction (Σ i : I, (get i))
  
  | subtype      {α : Type u} [topological_space α]
  (p : α → Prop)
  (h : abstraction α)
  : abstraction (subtype p)
  
  | quotient     {α : Type u} [topological_space α]
  (s : setoid α)
  (h : abstraction α)
  : abstraction (quotient s)
  
  instance particular (s : ω.substance) : ω.abstraction s.state := abstraction.particular s 
  
  -- CONCEPTS
  
  -- A concept for a Type is a topology
  -- for that Type that was abstracted away
  -- from the particular substances.
  -- It is a "concrete universal", an
  -- universal not defined up to isomorphism.
  structure concept (ω : ontology) : Type (u+1) :=
    (state : Type u)
    [t : topological_space state . tactic.apply_instance]
    [abs : ω.abstraction state . tactic.apply_instance]
  
  def substance.concept (s : ω.substance) : ω.concept := ⟨s.state⟩

  instance concept_top (c : ω.concept) : topological_space c.state := c.t
  
  instance concept_abs (c : ω.concept) : ω.abstraction c.state := c.abs
  
  -- concepts are inhabited by the concept of a
  -- necessary being.
  instance concept_inhabited : inhabited ω.concept := ⟨ω.nb.concept⟩
  
  variable c : ω.concept
  
  @[reducible]
  def concept.event := set c.state
  
  -- Concepts can have world indexed states just as substances
  -- but the concept doesnt just make sense for just any concept,
  -- so occasionally we can associate a nonempty set of states to
  -- a concept and occasionally it will be empty 
  -- (namely, if the concept is defined as a subconcept of another concept).
  def concept.state_at (w : ω.world) : c.event :=
    begin
      cases c,
      induction c_abs,
      exact {c_abs.state_at w},
      all_goals {
      dunfold concept.event concept.state,
      -- simp,
      },
      repeat {
      have ih : Π (i : c_abs_I), set (c_abs_get i) := c_abs_ih,
      intro x,
      },
      exact ∀i, x i ∈ ih i,
      exact x.snd ∈ ih x.fst,
      exact {x | x.val ∈ c_abs_ih},
      exact (@quotient.mk _ c_abs_s) '' c_abs_ih,
    end
  
  -- Given this we can define the notion of
  -- a map between state spaces preserving states.
  def state_preserving {c₁ c₂ : ω.concept} (f : c₁.state → c₂.state) :=
  ∀ w, f '' (c₁.state_at w) ⊆ c₂.state_at w
  
  -- An abstract quality is the analogue for concepts
  -- of the perfections of substances.
  structure concept.quality :=
  (exist : c.event)
  (is_open : is_open exist)
  (ne : exist.nonempty)
  (nuniv : exist ≠ univ)
  
  -- check whether an event is a quality
  def concept.is_quality (e : c.event):= is_open e ∧ e.nonempty ∧ e ≠ univ
  
  -- We can generate the set of substances which grounds a concept
  -- in reality. That is the set of substances from which the concept
  -- was abstracted.
  def concept.grounded (c : ω.concept) : set ω.substance :=
    begin
      cases c,
      induction c_abs,
      exact {c_abs},
      repeat{exact ⋃ i, c_abs_ih i},
      repeat{assumption},
    end
      
  -- Given a set of substances it is possible to
  -- construct different types of wholes/totalities
  -- which contain the set
  def integral_whole (s : set ω.substance) : ω.concept :=
    let get := λx : subtype s, x.val.state,
    type := Π i : subtype s, (get i)
    in begin
      set abs := @abstraction.pi ω _ get (by apply_instance) (by apply_instance),
      exact @concept.mk ω type _ abs,
    end
  
  def abstract_whole (s : set ω.substance) : ω.concept :=
    let get := λx : subtype s, x.val.state,
    type := Σ i : subtype s, (get i)
    in begin
      set abs := @abstraction.sigma ω _ get (by apply_instance) (by apply_instance),
      exact @concept.mk ω type _ abs,
    end 
  
  -- UNIVERSALS
  
  -- Since universals will 
  -- be equivalence classes of concepts, 
  -- we need to define a setoid of concepts.
  
  -- Two concepts are equivalent if they are homeomorphic
  @[reducible]
  def concept_equiv (c₁ c₂ : ω.concept) :=
  nonempty (c₁.state ≃ₜ c₂.state)
  
  instance concept_setoid : setoid ω.concept :=
  begin
  fconstructor,
  exact concept_equiv,
  repeat{constructor};
  simp [reflexive, symmetric, transitive],
  intro x,
  exact ⟨homeomorph.refl x.state⟩,
  intros x y h,
  constructor,
  exact homeomorph.symm h,
  intros x y z h₁ h₂,
  constructor,
  exact homeomorph.trans h₁ h₂,
  end
  
  -- finally
  def universal (ω : ontology) := @quotient ω.concept (by apply_instance)
  
  -- In order to the define the concept of `essence` and that of
  -- `definition` we require the definition of an invariant property.
  @[reducible]
  def property := ω.concept → Prop
  def property.invariant (p : property) :=
  ∀ c₁ c₂ : ω.concept, 
  c₁ ≈ c₂ → (p c₁ ↔ p c₂)
  
  -- The essence of an universal is a property which defines
  -- its concepts up to homeomorphism.
  def universal.is_essence (u : ω.universal) (p : property) :=
  p.invariant ∧
  ∃ c₁, ⟦c₁⟧ = u ∧ p c₁ ∧
  (∀ c₂, p c₂ → c₁ ≈ c₂)
  
  @[reducible]
  def universal.essence (u : ω.universal) := subtype u.is_essence
  
  -- every universal has an essence
  theorem essentialism : ∀ u : ω.universal, nonempty u.essence :=
  begin
  intro u,
  -- Take a representative concept c,
  -- then equivalence with c is the essence of u.
  -- Do note however that this essence is noncomputable,
  -- because u.out depends on classical.choice.
  -- So even though we know that every universal has an
  -- essence we do not know (in more concrete terms)
  -- the essence of every universal.
  -- Now, if instead we defined this in terms of concepts we
  -- would be able to construct the essence, therefore it makes
  -- more sense philosophically to only define essence for universals.
  let c := u.out,
  repeat{fconstructor},
  exact (≈) c,
  simp [property.invariant],
  suffices h : ∀ (c₁ c₂ : ω.concept), c₁ ≈ c₂ → (c ≈ c₁ → c ≈ c₂),
  intros c₁ c₂ h₂,
  have h₃ : c₂ ≈ c₁ := setoid.symm h₂,
  exact ⟨h c₁ c₂ h₂, h c₂ c₁ h₃⟩,
  intros c₁ c₂ h₁ h₂,
  exact setoid.trans h₂ h₁,
  exact c,
  simp [c],
  simp,
  end
  
  
  -- In another sense u.out, for u an universal, might be considered to be
  -- the essence of u, since it is an "abstract" representative of u.
  -- In this sense we could consider (e.g.) "the" natural numbers 
  -- to be an "essence" of sorts, because given the class of all models of
  -- second order arithmetic, neither a particular model nor the class itself
  -- appears to be a good candidate for "the" natural numbers, but an abstract
  -- representative of the class appears to be it. In this sense we can
  -- somewhat avoid the "up to isomorphism" restriction placed upon mathematical
  -- concepts. A restriction which, if we were to be consistent with it, should
  -- preclude us from talking about "the" natural numbers at all.
  
  -- It appears to be the same thing for most purposes to either take
  -- u.out as the essence or the relation of "being homeomorphic to u.out"
  -- as the essence. Although it would look like the first point of view
  -- is the traditional essentialist one, while the second appears to be
  -- some form of similarity nominalism. Arguably even this similarity 
  -- view is a pretty essentialistic one insofar as the representative u.out
  -- is totally abstract and impossible to concretely construct or to.
  -- concretely compare with anything except by means of essential invariant
  -- properties which are necessarilly true for all instances of an universal.
  
  -- In this the noncomputable nature of classical.choice can be given 
  -- a philosophical interpretation, since we cannot compute or construct
  -- abstract essences, otherwise they would be concrete.
  
  -- The representation u.out also acts as a generic instance of the universal.
  -- For any given invariant property, suffices to show that it is valid
  -- for u.out to conclude it is valid for any representation.
  -- An example of this is given below:
  
  -- A concept is instantiable if it is homeomorphic to the state
  -- space of a substance, so that it could be thought as being an
  -- entity of the same species as that substance.
  def instantiable (ω : ontology) : property := λc, ∃ s : ω.substance, s.concept ≈ c
  
  -- Instantiability is of course an invariant
  lemma concept_instantiable_invariant : ω.instantiable.invariant :=
  begin
  dunfold instantiable property.invariant,
  intros c₁ c₂ h,
  suffices c : (∃ (s : ω.substance), substance.concept s ≈ c₁) → ∃ (s : ω.substance), substance.concept s ≈ c₂,
  constructor,
  exact c,
  all_goals{
  intro hs,
  obtain ⟨s, hs⟩ := hs,
  existsi s,
  },
  exact setoid.trans hs (setoid.symm h),
  exact setoid.trans hs h,
  end
  
  -- Therefore we define instantiablity for universals via quotient.out
  def universal.instantiable (u : ω.universal) := ω.instantiable u.out
  
  -- TODO: argue that Aquinas defended the u.out point of view in
  -- De ente et essentia.
  
  -- The nb as an universal.
  @[reducible]
  def nbu (ω : ontology) : ω.universal := ⟦ω.nb.concept⟧
  instance universal_inhabited : inhabited ω.universal := ⟨ω.nbu⟩
  
  -- A notion is a quality defined abstractly in the representation
  def universal.notion (u : ω.universal) := u.out.quality 
  
  
end ontology