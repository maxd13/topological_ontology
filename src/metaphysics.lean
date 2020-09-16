import states
universe u
open set topological_space classical
local attribute [instance] prop_decidable

namespace ontology

    variables {ω : ontology} (s : ω.substance)
    
    section metaphysics
    
        -- We call a substance `metaphysical`, or a `separate substance`, if it is simple.
        -- It is otherwise `physical`, or a `body`, as already mentioned.
        @[reducible]
        def substance.metaphysical := simple s.val
        def separate (ω : ontology) := subtype {s : ω.substance | s.metaphysical}
        
        -- A substance is purely actual if it has no passive potency
        -- to be different from what it is, i.e. if it has a single state.
        def substance.purely_actual := nonempty (s.state ≃ unit)
        
        -- Only the necessary being can be purely actual, 
        -- in which case platonism follows.
        -- def eq_nb_of_purely_actual : ∀ s, purely_actual s → s = nb :=
        -- begin
        --     intros s h,
        --     simp [purely_actual] at h,
        --     apply nonempty.elim h,
        --     intro iso,
        --     simp [substance.state, substance.state_setoid, quotient] at iso,
            
        -- end

        theorem metaphysical_of_purely_actual : s.purely_actual → s.metaphysical  := sorry
        
        -- Platonism in the broad sense is the doctrine 
        -- that there are metaphysical substances
        def platonism (ω : ontology) := nonempty ω.separate

        -- theism is the doctrine that the necessary being is metaphysical.
        def theism (ω : ontology) := ω.nb.metaphysical
        
        -- Platonism is logically equivalent to theism
        lemma platonism_of_nonempty_separate :  ω.platonism ↔ ω.theism := sorry
        
    end metaphysics

    section theology
    
        -- Classical Theism is an extension of theism which 
        -- furthermore claims that there is a possible world 
        -- in which the necessary being exists alone.
        def classical_theism := ω.theism ∧ ∃ (w : ω.world), world.entities w = {ω.nb.val}

        -- greek theism is non-classical theism
        def greek_theism := ω.theism ∧ ¬ ∃ (w : ω.world), world.entities w = {ω.nb.val}
    
    end theology
end ontology