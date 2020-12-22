import metaphysics.causality metaphysics.finitism states
universe u
open set topological_space classical
local attribute [instance] prop_decidable

namespace ontology
    
  variables {ω : ontology} (s : ω.substance)

  -- (strong) Platonism is the doctrine 
  -- that there are simple substances
  def splatonism (ω : ontology) := ∃ s : ω.substance, s.simple

    section theology
        
        -- The leibnizian version of a weakened version of Aquina's second way.
        -- Possibly the weakest argument anyone can give for the existence of God.
        theorem weak_leibnitz2 : ω.epsr.nonempty → ω.theism :=
            begin
                simp [set.nonempty, epsr],
                intros w psr,
                dunfold theism substance.simple simple,
                -- suppose God had an accident
                by_contradiction h,
                push_neg at h,
                -- then He should also have an accident 'a' 
                -- in the world w in which psr is valid
                have c₀ : ∃ (a : entity ω), a.subsists (nb ω).val ∧ a ≠ (nb ω).val ∧ a ∈ w,
                    admit,
                obtain ⟨a, a_subs, a_contingent, H⟩ := c₀,
                -- this accident has a cause in w, call it 's'.
                have c₁ := psr a a_contingent H,
                simp [entity.caused] at c₁,
                obtain ⟨s, hs⟩ := c₁,
                -- But this cause would in a sense have to be a
                -- cause of something that is going on in the necessary
                -- being.
                have c₂ : s.causes ω.nbe.exist w,
                    admit,
                -- However the necessary being admits no causes.
                have c₃ : ¬ ∃ s : ω.substance, s.causes ω.nbe.exist w,
                    admit,
                push_neg at c₃,
                specialize c₃ s,
                contradiction,
                -- Therefore the necessary being 
                -- is what we call God (E.Q.D.D.).



                -- by_cases c₀ : ∃ e : ω.entity, e ∈ w ∧ e.contingent,
                --     swap,
                --     admit,
                -- obtain ⟨e, H, hce⟩ := c₀,
                -- have c₁ := psr e hce H,
                -- obtain ⟨g, uncaused, cause⟩ := pp e c₁,
                -- simp [entity.uncaused] at uncaused,
                -- have c₂ : ¬ g.val.contingent,
                --     intro h,
                --     simp [ substance.causes
                --          , entity.sdepends
                --          , entity.depends
                --          , event.sdepends
                --          , event.depends
                --          ] at cause,
                --     have gexists := cause.1.2.1,
                --     specialize psr g.val h gexists,
                --     contradiction,
                -- simp [entity.contingent] at c₂,
                -- rw c₂ at uncaused,
                -- simp [entity.caused, substance.causes, event.sdepends] at uncaused,
                -- simp [theism, substance.metaphysical, simple],
                -- intros x sx,
                -- -- specialize uncaused x,
                -- -- simp at uncaused,
                -- admit,
            end


        -- Aquina's second way, weakened so as to use pp instead of
        -- any stronger assumptions, and which assumes only the
        -- conjoint possibility of the premisses.
        
        -- A slightly stronger argument can prove classical
        -- theism. Since weak substantial finitism is strictly stronger
        -- than pp, it should also follow that we cannot prove classical
        -- theism from pp alone. I wonder if we can prove it
        -- from causal finitism?
        theorem wsf_aquinas2 : ω.psr → ω.wsfinitistic → ω.ctheism :=
            begin
                intros psr wsf,
                obtain ⟨w₀, hw₀⟩ := wsf,
                admit,
            end

    
    end theology
end ontology