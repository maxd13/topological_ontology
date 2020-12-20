import 
    -- data.real.basic
    -- topology.instances.real
    -- measure_theory.borel_space
    -- measure_theory.measure_space
    states

universe u
open set topological_space classical
local attribute [instance] prop_decidable

/-! # State Spaces

Here we develop the higher order consequences of our theory,
which are a consequence of the notion of state. We expand
the notion of state to define state spaces for substances,
and prove associated lemmas.

We adopt the convention that all dependent types of a substance
are to be upper cased, so for instance the type of states of a 
substance `s` is `s.State`.

-/

-- TODO: refactor so our naming convention is valid.
-- TODO: refactor proofs so they are correct under the
-- new definition of states (they worked before).

namespace ontology
 
 variables {ω : ontology} (s : ω.substance)
 include ω
 
 
 -- The type of states of a substance
 @[reducible]
 def substance.State := quotient s.State_setoid
 
 -- The quotient map from worlds to states,
 -- which ontologically grounds set of states as entities.
--  @[reducible]
--  def substance.f := @quotient.mk ω.world s.State_setoid
 
 @[reducible]
 def substance.State_at (w : ω.world) := @quotient.mk ω.world s.State_setoid w
 
 -- Recall that the quotient of a topological space
 -- is itself a topological space. Therefore the type
 -- of states of a substance is naturally endowed with 
 -- topological structure. A set of states will be open 
 -- if and only if the set of all worlds in which the substance is
 -- in one of the states is itself open, so any nonempty set of states
 -- can only be open if there is some entity which exists precisely in
 -- the worlds in which the entity has one of those states. 
 -- Therefore any nonempty set of states is ontologically grounded,
 -- and so we can consider any such set to be an ontologically grounded
 -- property of the substance, and this we call a perfection.
 
 @[reducible]
 def substance.Event := set s.State
 
 structure substance.Perfection :=
    -- the event of the perfection existing in the substance
    (exist : s.Event)
    (is_open : is_open exist)
    (ne : exist.nonempty)
    (nuniv : exist ≠ univ)
 
 -- We added nuniv because the necessary s.Event should not really
 -- be considered an internal perfection of the substance, since it
 -- is grounded in the nb and is always necessary.
 
 -- Accidents of a substance are perfections of the same substance.
 -- The most important step in this proof is to show that they are open.
 lemma state_open_of_accident : ∀ (a: ω.accident), a.inheres s → is_open (s.State_at '' a.val.exist) := sorry
--  begin
--     intros a H,
--     apply is_open_coinduced.2,
--     simp [preimage],
--     let α := {x : ω.world | ∃ (x_1 : ω.world), x_1 ∈ (a.val).exist ∧ substance.equiv s x_1 x},
--     suffices c : is_open α,
--         exact c,
--     suffices c : α  = a.val.exist,
--         rw c,
--         exact a.val.is_open,
--     ext, constructor; intro h; simp at *,
--         obtain ⟨y, h₁, h₂⟩ := h,
--         simp [substance.equiv, substance.state] at h₂,
--         simp [ontology.world.entities, entity.subsistents] at h₂,
        
--         -- have c : {a : ω.accident | a.inheres s} ∩ {a : ω.accident | y ∈ (a.val).exist} ⊆
--         --          {a : ω.accident | a.inheres s} ∩ {a : ω.accident | x ∈ (a.val).exist},
--         -- rw h₂,
--         -- exact and.right (@c a ⟨H, h₁⟩),
--     existsi x,
--     constructor,
--         assumption,
--     obtain ⟨res, _, _⟩ := substance.equiv_sound s,
--     exact res x,
--  end
 
 -- It should then be easier to prove that it is not empty
 lemma state_ne_of_accident : ∀ (a: ω.accident), a.inheres s → (s.State_at '' a.val.exist).nonempty :=
 begin
    intros a H,
    simp [preimage],
    exact a.val.ne,
 end
 
 -- But it is a little bit harder to prove it is not univ
 lemma state_nuniv_of_accident : ∀ (a: ω.accident), a.inheres s → (s.State_at '' a.val.exist) ≠ univ := sorry
--  begin
--     intros a H,
--     simp [preimage, image, quotient.mk],
--     intro h,
--     -- This is a trick
--     -- let ψ := (@quotient.mk world ontology.substance.State_setoid),
--     replace h : univ ⊆ {b : quotient s.State_setoid | ∃ (a_1 : ω.world), a_1 ∈ (a.val).exist ∧ s.State_at a_1 = b},
--         rw ←h,
--         -- refl,
--     have c : s.val.exist = a.val.exist,
--     ext, constructor; intro h₁,--; simp at *,
--         have c := @h (s.State_at x) _,
--         simp at c,
--         obtain ⟨y, c₁, c₂⟩ := c,
--         replace c₂ : s.equiv y x := c₂,
--         simp [substance.equiv, substance.state] at c₂,
--         simp [ontology.world.entities, entity.subsistents] at c₂,
--         have c : {a : ω.accident | a.inheres s} ∩ {a : ω.accident | y ∈ (a.val).exist} ⊆
--                  {a : ω.accident | a.inheres s} ∩ {a : ω.accident | x ∈ (a.val).exist},
--         rw c₂,
--         exact and.right (@c a ⟨H, c₁⟩),
--             trivial,
--         revert x,
--         apply sub_of_inheres,
--         exact H,
--     have c₁ : s.val.exist.dense := s.property,
--     have c₂ : ¬ a.val.exist.dense := a.property,
--     rw c at c₁,
--     contradiction,
--  end
 
 -- Finally we can construct the perfection.
 def substance.Perfection_of (a ∈ s.accidents) : s.Perfection :=
    ⟨ s.State_at '' a.val.exist
    , state_open_of_accident s a H
    , state_ne_of_accident s a H
    , state_nuniv_of_accident s a H
    ⟩
 
 -- perfections which come from accidents
 @[reducible]
 def substance.aperfections := {p : s.Perfection | ∃ a ∈ s.accidents, (s.Perfection_of a H) = p}
 
 -- events which come from accidents
 @[reducible]
 def substance.aevents := {p : s.Event | ∃ a ∈ s.accidents, (s.Perfection_of a H).exist = p}
 
 instance state_has_mem : has_mem s.Perfection s.State :=
 ⟨λ p s, s ∈ p.exist⟩
 @[reducible]
 def perfections (x : s.State) := {p : s.Perfection | p ∈ x}
 
 -- We can also build a neighborhood for any state
 -- which is an aperfection in case the substance has
 -- accidents in that state and the whole space otherwise.
 
 structure nhd {s : ω.substance} (x : s.State) :=
    (U : s.Event)
    (is_open : is_open U)
    (elem : x ∈ U)
 
 noncomputable def state.nhd_default {s : ω.substance} (x : s.State) : nhd x :=
    begin
        classical,
        set elab_help := s.State_setoid,
        -- lets build a world which maps to x
        -- and has some accident, the associated perfection of which
        -- will be our neighborhood. If no such world exists, we
        -- will just use univ.
        by_cases w : ∃w, ⟦w⟧ = x ∧ (∃a : ω.accident, a.inheres s ∧ a.val ∈ w),
        swap,
            exact ⟨univ, is_open_univ, by simp⟩,
        replace w := nonempty_subtype.2 w,
        replace w := classical.choice w,
        obtain ⟨w, hw, a⟩ := w,
        replace a := nonempty_subtype.2 a,
        replace a := classical.choice a,
        obtain ⟨a, ha₁, ha₂⟩ := a,
        -- a is now our wanted accident.
        let p := s.Perfection_of a ha₁,
        -- it is now easier to build the neighborhood.
        fconstructor,
            exact p.exist,
            exact p.is_open,
        rw ←hw,
        simp [p,substance.Perfection_of],
        existsi w,
        exact ⟨ha₂, rfl⟩,
    end
 
 -- Each contingent substance has a bottom state. For a contingent substance
 -- this is the "state" in which the substance does not exist.
 
 --  lemma aux : contingent s → ∀ w, 
 
 --  def aux (h : contingent s) : nonempty (subtype s.val.exist.compl) := sorry
  
 --  @[reducible]
 --  noncomputable def state_bot (h : contingent s) : s.State :=
 --      have c : ¬ ∀ x, x ∈ s.val.exist,
 --         by {obtain ⟨⟨exist, is_open, nes⟩, perfect⟩ := s,
 --             intro h',
 --             replace h' := eq_univ_of_forall h',
 --             simp [contingent, nb, nbe] at h,
 --             simp at h',
 --             contradiction,
 --            },
 --     --  φ $
 --     --  classical.choice $
 --     --  nonempty_of_exists $
 --     --  not_forall.mp c
 --     -- have d : nonempty (subtype s.val.exist.compl),
 --     --     begin 
 --     --         replace c := not_forall.mp c,
 --     --         obtain ⟨x, hx⟩ := c,
 --     --         constructor,
 --     --         exact ⟨x, hx⟩,
 --     --     end,
 --     φ $
 --     subtype.val $
 --     choice $
 --     aux h
        
 
 
 
 --   begin
 --     classical,
 --     obtain ⟨⟨exist, is_open, nes⟩, perfect⟩ := s,
 --     simp [contingent, nb, nbe] at h,
 --     set s : ω.substance := ⟨⟨exist, is_open, nes⟩, perfect⟩,
 --     have c : ¬ ∀ x, x ∈ exist,
 --         intro h',
 --         replace h' := eq_univ_of_forall h',
 --         contradiction,
 --     replace c := not_forall.mp c,
 --     replace c := nonempty_of_exists c,
 --     replace c := classical.choice c,
 --     exact φ s c,
 --   end
 
 -- set_option trace.elaborator_detail true
 --  lemma bot_no_accidents (h : contingent s) : (s.State_set (@quotient.out _ s.State_setoid (state_bot h))) = ∅ :=
 --     begin
 --         set elab_help := s.State_setoid,
 --         simp [substance.State_set],
 --         apply eq_empty_iff_forall_not_mem.2,
 --         intro x,
 --         simp,
 --         -- simp [state_bot, ontology.φ],
 --         intros h₂ h₃,
 --         -- simp at h₃,
 --         have d := sub_of_inheres x s h₂,
 --         replace h₃ := d h₃,
 --         -- simp [(choice (aux s h)).property] at h₃,
 --         -- set c := subtype.val (choice (aux s h),
 --         -- let c := quotient.mk_out ⟦(choice (aux s h)).val⟧,
 --         -- simp [quotient.out],
 --     end
 
 -- The bottom has no perfections.
 -- For the necessary being it is rather that
 -- we should consider it to have a single necessary
 -- informal "perfection" which is the set which 
 -- contains only the unique state of the nb.
 --   lemma state_bot_empty : perfections ⊥ = ∅ :=
 --    begin
 --     classical,
 --     set elab_help := s.State_setoid,
 --      simp [perfections],
 --      apply eq_empty_of_subset_empty,
 --      intros p hp,
 --      simp at *,
 --      let e := quotient.mk⁻¹' p.exist,
 --      let state := p.ne.some,
 --      have c : is_open e ∧ e.nonempty,
 --         constructor,
 --         exact p.is_open,
 --         simp [set.nonempty],
 --         use state.out,
 --         simp,
 --         exact p.ne.some_mem,
 --     let e₂ : entity := ⟨e, c.1, c.2⟩, 
 --         -- apply mem_preimage.2,
 --         -- exact p.ne,
 --         -- focus {library_search},
 --     --  by_cases contingent s;
 --     --  simp [has_bot.bot, h, has_mem.mem] at hp,
      
 --    end
 
 -- Every state space is T0 but not T1, so that its specialization order
 -- has a botton element. For a contingent substance
 -- this is the "state" in which the substance does not exist.
 -- For the necessary being it is its unique state.
 --  instance state_order_bot : order_bot s.State :=
 --   begin
 --     classical,
 --     fconstructor,
 --         by_cases contingent s,
 --             obtain ⟨⟨exist, is_open, nes⟩, perfect⟩ := s,
 --             simp [contingent, nb, nbe] at h,
 --             set s : ω.substance := ⟨⟨exist, is_open, nes⟩, perfect⟩,
 --             have c : ¬ ∀ x, x ∈ exist,
 --                 intro h',
 --                 replace h' := eq_univ_of_forall h',
 --                 contradiction,
 --             replace c := not_forall.mp c,
 --             replace c := nonempty_of_exists c,
 --             replace c := classical.choice c,
 --             exact φ s c,
 --         exact φ s (default world),
 --     intros x₁ x₂,
 --     exact ∀ p : s.Perfection, p ∈ x₁ → p ∈ x₂,
 --         intros x p h,
 --         exact h,
 --     intros x y z h₁ h₂ p hp,
 --     exact h₂ p (h₁ p hp),
 --         intros x y h₁ h₂,
 --         admit,
 --     intros x p hp,
 --     by_cases contingent s;
 --     simp [h] at hp,
 --   end
 
 
 -- Next we wish to show that the perfections which come from accidents
 -- form a basis.
 --  lemma accidents_nhds : ∀ (w : s.State) (U : set s.State), w ∈ U → is_open U → ∃ V ∈ s.aevents, w ∈ V ∧ V ⊆ U :=
 --  begin
 --      intros w U H op,
 --  end
 
 --  #check is_topological_basis_of_open_of_nhds
 
 -- Then we want to show that unions of accidents also map
 -- to perfections, and that all perfections are generated this way.
 
end ontology