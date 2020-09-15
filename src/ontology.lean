import 
    topology.bases
    topology.order 
    topology.homeomorph
    topology.subset_properties
    -- data.real.basic
    -- topology.instances.real
    -- measure_theory.borel_space
    -- measure_theory.measure_space
    tactic.tidy
universe u
open set topological_space classical
local attribute [instance] prop_decidable

/-! 

# A topological formal ontology and foundation of philosophy

The purpose of this work is to implement an 
upper level ontology that minimizes the number of primitive terms and axioms,
while maximizing explanatory power with regards to the interpretability of 
philosophical concepts in the theory. We seek to give to the whole of philosophy the same sort
of rigorous foundation that set theory gives to mathematics, in terms of possible entities and possible
worlds.

Among other things, we seek to precisely define in our theory the concepts of: substance, physical substance,
metaphysical substance, accident, concept, universal, property, positive property, the process of abstraction,
matter, form, the categories of being, the predicaments, essence and existence, causality, parthood, God, theism,
atheism, physicalism, monism, pantheism, eleaticism, platonism, modal realism.
We also seek to formalize theories of: causality, mereology,
epistemology, ethics, philosophy of nature, metaphysics and natural theology. 
All of it based on the foundation of possible worlds and possible entities.

Pretty audacious, ain't it?

I am actually undecided about whether I need a theory of counterfactuals. 
But anyone should be able to create his own theory of counterfactuals based on these foundations,
if he so wishes.

## Ontologies and Events

The fundamental concept on which all of our work is based upon, is the concept of an *ontology of possible worlds*.
Which is to be comprised of a Type of possible worlds equipped with some fundamental topological structure, 
the philosophical significance of which shall be made clear shortly.

The notion of possible world is of course a primitive one, and you may interpret it as you will. 
We take a possible world in our theory to be a point in the phase space of the whole of possible reality,
a fully qualified description of a possible state of existence, 
the outcomes of the most general random experiment one could possible make, etc...

More importantly, given this primitive notion we can readily define the notion of an ontological 
**Event** as simply a set of possible worlds; the notion should be familiar to those acquainted 
with probability theory (probability spaces). An event is something that "happens" or "occurs", 
precisely in the possible worlds which compose it, i.e. an event is the set of all possible worlds in which
the event occurs. We would like to talk a little bit about events before delving into the mathematical definitions.

Another way to see an event is as (the semantic content of) a proposition. 
Not all events are necessarily propositions 
(because we could have uncountably many events, but countably many propositions) 
but every proposition is to be associated with an event: 
the set of all possible worlds in which the proposition is true.
For instance the proposition "Socrates exists" corresponds to the event {w : world | Socrates exists in w}.

Now, it is quite clear that some propositions "talk about" or postulate one or more things existing, while others do not. 
"Socrates exists" clearly postulates the existence of Socrates, just as "Humans exist" postulates the existence of 
Human beings, and "Socrates and Plato exist" postulates the existence of both Plato and Socrates, etc... 
On the other hand, "Unicorns do not exist", does not seem to postulate or "talk about" 
the existence of anything, but merely about the *absence* of an existence. 
So there is quite clearly a primitive notion of which propositions 
talk about existence and which do not. 

For the sake of generality we can take this notion to apply to all events regardless
of whether they are proposition or not, and stop talking about propositions altogether.
So an event will be **existential** or **open** 
precisely when its occurrence postulates that one or more entities from a set of entities must exist,
which is to say that the event can only occur in a possible world if those entities it postulates 
do exist in that possible world.

Now, as we have already exemplified, we should expect that arbitrary set unions of existential 
events be existential events, since the event "(Some)Humans exist" is the union of all events of the form
"X exists" for any possible human X. The same should apply for intersections, since "All possible humans exist" 
is the intersection of "X exists" for any possible human X. An generally speaking, for any arbitrary family
of existential events, we should exp



Hence we define an ontology as a nonempty T0 Alexandroff topological space of possible worlds:

-/


structure pre_ontology : Type (u+1) :=
    (world : Type u)
    [ne : nonempty world . tactic.apply_instance]
    [t : topological_space world . tactic.apply_instance]

instance pre_ontology_top  (ω : pre_ontology)  : topological_space ω.world := ω.t
instance pre_ontology_ne  (ω : pre_ontology)  : nonempty ω.world := ω.ne

-- An `ontology` is a nonempty T0 topological space
-- of possible worlds.
structure ontology extends pre_ontology  :=
    [axiom₀ : t0_space world . tactic.apply_instance]

instance ontology_t0  (ω : ontology)  : t0_space ω.world := ω.axiom₀

-- TODO: define a stronger ontology type which assumes the space is Alexandroff
-- uncountable, substantially finite and has the property that no world is disconnected
-- in the specialization pre-order, in the sense that there must either be a world 
-- below it or one above it. This depends on a previous module alexandroff_space.lean
-- being defined.

/-!

## Extension and intension

-/

namespace ontology

variable {ω : ontology}

-- We introduce first the notion of events. 
section events

 -- Events in an ontology are simply sets of worlds.
 -- Events (informally) are said to `occur` precisely in their element worlds.
 @[reducible, alias]
 def event (ω : ontology) := set ω.world 
 
 variable (e : ω.event)
 
 -- We define the related topological notions for events.
 @[reducible]
 def event.interior := interior e
 @[reducible]
 def event.closure  := closure e
 @[reducible]
 def event.dense := closure e = univ
 @[reducible]
 def event.exterior : ω.event := interior (-e)
 @[reducible]
 def event.regular := e = e.exterior.exterior
 -- also called boundary
 @[reducible]
 def event.frontier (e : ω.event) := frontier e
  
end events

-- And we prove some simple useful lemmas about them 
section event_lemmas

 variable {e : ω.event} 
 lemma event_union_exterior_open : is_open e → is_open (e ∪ e.exterior) :=
    begin
      intro h,
      apply is_open_union h,
      simp [event.exterior],
    end

 -- For some reason in the standard library there is a lemma
 -- like this for finsets but not one for sets.
 lemma event_nonempty_of_ne_empty : e ≠ ∅ → e.nonempty :=
    begin
        intro h,
        simp [set.nonempty],
        classical,
        by_contradiction h₂,
        replace h₂ := forall_not_of_not_exists h₂,
        simp at h₂,
        replace h₂ := eq_empty_iff_forall_not_mem.2 h₂,
        contradiction,
    end

 lemma event_union_exterior_nonempty : (e ∪ e.exterior).nonempty :=
    begin
       apply event_nonempty_of_ne_empty,
       intro h,
       simp at h,
       obtain ⟨h₁, h₂⟩ := h,
       rw h₁ at h₂,
       simp [event.exterior] at h₂,
       have c := ω.ne,
       contradiction,
    end

end event_lemmas

-- We define entities to be particular kinds of events.
section entities 
 
 -- Particular (possible) `entities` in the ontology are nonempty open sets of worlds.
 -- An entity is said to `exist` precisely in those worlds which are its elements.
 structure entity (ω : ontology) :=
      -- the event of the entity existing
      (exist : ω.event)
      (is_open : is_open exist)
      (ne : exist.nonempty)
  
 variables (e e₁ e₂ : ω.entity)
 
 -- Two entities are `contrary` if their intersection (as sets) is empty,
 -- they are otherwise `compatible`.
 @[reducible]
 def entity.contrary := e₁.exist ∩ e₂.exist = ∅
 @[reducible]
 def entity.compatible := (e₁.exist ∩ e₂.exist).nonempty
 
 -- Some very important entities have no contraries
 @[reducible]
 def entity.nocontrary := ¬ ∃ y, e.contrary y
 
 -- Entity x is said to existentially entail entity y,
 -- or to existentially depend on y,
 -- if in every possible world in which x exists, y exists.
 -- For this relation we use the subset notation.
 
 instance entity.has_subset : has_subset ω.entity := 
      ⟨λ x y : ω.entity, x.exist ⊆ y.exist⟩

 -- The necessary being (entity) is the entity which exists in
 -- every possible world.
 def nbe (ω : ontology) : ω.entity := ⟨univ,is_open_univ, by simp [empty_ne_univ]⟩
 
 -- Here are some definitions which look more like lemmas,
 -- these ones are more philosophical.
 
 -- Arbitrary nonempty unions of entities are entities.
 def entity_Sup (s : set ω.entity) (h : s.nonempty) : ω.entity :=
   begin
      fsplit,
          exact ⋃ i ∈ s, entity.exist i,
      apply is_open_bUnion,
      intros i H,
      exact i.is_open,
          simp [set.nonempty],

      let i := h.some,
      let w := i.ne.some,
      existsi w,
      existsi i,
      constructor,
        exact h.some_mem,
        exact i.ne.some_mem,
   end
  
 -- Nonempty finite intersections of entities are entities
 def entity.inter (h : e₁.compatible e₂) : ω.entity :=
      ⟨  e₁.exist ∩ e₂.exist
      , is_open_inter e₁.is_open e₂.is_open
      , h
      ⟩
  
 -- We can also talk about an entity existing in a world
 -- as belonging to it, so we can use the notation e ∈ w.
 @[reducible]
 instance world.has_mem : has_mem ω.entity ω.world := ⟨λe w, w ∈ e.exist⟩
 @[reducible]
 def world.entities (w : ω.world) := {e : ω.entity | e ∈ w}

end entities

-- We next define substances as particular kinds of entities.
-- Accidents are also defined here.
section substances

 -- Particular `substances` in the ontology are dense entities, every other entity is an `accident`.
 -- We also call a dense entity a perfect entity.
 @[reducible]
 def perfect (e : ω.entity) := e.exist.dense
 @[reducible]
 def imperfect (e : ω.entity) := ¬ perfect e
 def substance (ω : ontology) := subtype {e : ω.entity | perfect e}
 def accident (ω : ontology) := subtype {e : ω.entity | imperfect e}
 
 -- By this definition, it is obvious that any entity 
 -- is either a substance or an accident, therefore we can
 -- cast it to one of them.
 
 noncomputable def antepredicament (e : ω.entity) : ω.substance ⊕ ω.accident :=
  begin
      by_cases perfect e,
          left,
          exact ⟨e, h⟩,
      right,
      exact ⟨e, h⟩,
  end

 -- The `necessary being` is the substance that exists in every possible world.
 def nb (ω : ontology) : ω.substance := 
       ⟨ω.nbe, by simp [nbe, set_of, perfect, event.dense]⟩
   
 instance substance.inhabited : inhabited ω.substance := ⟨ω.nb⟩
 
 -- A substance is `contingent` if it is not the necessary being.
 -- Since the nb is a substance, all accidents are informally contingent.
 def contingent (s : ω.substance) := s ≠ ω.nb
 
 @[reducible]
 def world.substances (w : ω.world) := {s : ω.substance | s.val ∈ w}
 @[reducible]
 def world.accidents (w : ω.world) := {a : ω.accident | a.val ∈ w}

end substances

-- We then prove some very important lemmas for substances which
-- motivate their definition.
section substance_lemmas

 -- The fundamental fact that justifies the definition of substances
 -- is that they admit no contrary entities, and this is a property
 -- explicitly mentioned in Aristotle's Categories, which suffices for
 -- their definition. 
 lemma substance_nocontrary : ∀ s : ω.substance, s.val.nocontrary :=
    begin
        intros s h,
        obtain ⟨e, h ⟩ := h,
        -- this is a crazy trick which helps me unfold a definition 
        -- 99% of the time. Idk why this works when simp[entity.contrary]
        -- doesn't.
        revert h,
        dunfold entity.contrary,
        intro h,
        let α := e.exist ∩ (s.val).exist,
        replace h : α = ∅,
            rwa inter_comm (s.val).exist e.exist at h,
        suffices c : α.nonempty,
            replace c := c.ne_empty,
            contradiction,
        apply dense_iff_inter_open.mp s.property,
            exact e.is_open,
        exact e.ne,
    end

 lemma perfect_iff_nocontrary : ∀ e : ω.entity, e.nocontrary ↔ perfect e :=
     begin
        intro e,
        constructor; intro h,
            simp [perfect, event.dense],
            revert h,
            dunfold entity.nocontrary,
            dunfold entity.contrary,
            intro h,
            replace h := forall_not_of_not_exists h,
            simp at h,
            apply dense_iff_inter_open.2,
            intros U h₁ h₂,
            replace h := h ⟨U, h₁, h₂⟩,
            simp at h,
            rwa inter_comm e.exist U at h,
            exact event_nonempty_of_ne_empty h,
        exact substance_nocontrary ⟨e, h⟩,
     end

 -- Any substance (existentially) depends only on other substances
 lemma substance_of_substance_entails : ∀{s : ω.substance}{e : ω.entity},
                                           s.val ⊆ e → perfect e :=
    begin
        intros s e h,
        simp [perfect, event.dense],
        have c₀ : closure (s.val.exist) = univ := s.property,
        have c₁ := closure_mono h,
        rw c₀ at c₁,
        have c₂ : closure (e.exist) ⊆ univ := subset_univ (closure (e.exist)),
        exact subset.antisymm c₂ c₁,
    end

 -- Arbitrary unions of substances are substances.
 def substance_Sup (s : set ω.substance) (h : s.nonempty) : ω.substance :=
    begin
      fsplit,
          apply entity_Sup (subtype.val '' s),
          simp,
          exact h,
      simp [set_of, perfect, event.dense, entity_Sup],
      let i := h.some,
      have c : i.val.exist ⊆ (⋃ (i : ω.substance) (H : i ∈  s), i.val.exist),
          intros w h₂,
          simp,
          existsi i,
          exact ⟨h.some_mem,h₂⟩,
      replace c := closure_mono c,
      have p : closure ((i.val).exist) = univ := i.property,
      rw p at c,
      exact eq_univ_of_univ_subset c,
    end
   
 -- Finite intersections of substances are substances
 def substance.inter (s₁ s₂ : ω.substance) : ω.substance :=
    begin
      fsplit,
          fsplit,
              exact s₁.val.exist ∩ s₂.val.exist,
          exact is_open_and s₁.val.is_open s₂.val.is_open,
              apply dense_iff_inter_open.mp s₂.property s₁.val.exist,
                  exact s₁.val.is_open,
                  exact s₁.val.ne,
      simp [set_of, perfect, event.dense],
      apply dense_iff_inter_open.2,
      intros U H ne,
      apply event_nonempty_of_ne_empty,
      intro h,
      let α := (U ∩ (s₁.val).exist) ∩ (s₂.val).exist,
      replace h : α = ∅,
          simp [α,inter_assoc, h],
      suffices c : α.nonempty,
          replace c := c.ne_empty,
          contradiction,
      apply dense_iff_inter_open.mp s₂.property,
          exact is_open_inter H s₁.val.is_open,
      exact dense_iff_inter_open.mp s₁.property U H ne,
    end
 instance substance.has_inter : has_inter ω.substance := ⟨substance.inter⟩
   
end substance_lemmas

-- We discuss the fundamental notion of subsistence, 
-- which provides further justification for our definition.
section subsistence

 -- An entity is said to `subsist` in another entity 
 -- if and only if the second can be written as the union of the first
 -- and its interior, or alternatively, as the complement of its boundary.
 
 @[reducible]
 def entity.subsists (e₁ e₂ : ω.entity) := e₁.exist ∪ e₁.exist.exterior = e₂.exist
 
 @[reducible]
 def entity.subsistents (e : ω.entity) := {x : ω.entity | x.subsists e}
 
 -- Inherence is the same relation defined between accidents and substances
 def accident.inheres (a : ω.accident) (s : ω.substance) := a.val.subsists s.val

 -- instance substance.has_mem : has_mem ω.accident ω.substance := ⟨accident.inheres⟩

 @[reducible]
 def substance.accidents (s : ω.substance) := {a : ω.accident | a.inheres s}

 -- Only substances can support accidents
 lemma sub_support :  ∀ {e}, (∃x : ω.entity, x.subsists e) → perfect e :=
  begin
      intros e h,
      obtain ⟨y, h⟩ := h,
      simp [perfect, event.dense],
      simp [entity.subsists] at h,
      rw ←h,
      simp [closure_union, event.exterior],
      ext, constructor; intro h₂,
          trivial,
      by_cases x ∈ closure (y.exist),
          simp [h],
      right,
      intro h₃,
      have c : x ∈ closure (y.exist) := interior_subset h₃,
      contradiction,
  end

 -- Every accident inheres in a single substance, 
 -- therefore we can construct the substance from the accident.
 def accident.owner (a : ω.accident) : ω.substance := 
      let e : ω.entity := ⟨a.val.exist ∪ a.val.exist.exterior,
                        event_union_exterior_open a.val.is_open,
                        event_union_exterior_nonempty⟩ 
      in ⟨e, sub_support ⟨a.val, rfl⟩⟩

end subsistence

-- We prove important lemmas about subsistence and inherence.
section subsistence_lemmas
 
 variables (e e₁ e₂ : ω.entity) {a : ω.accident} {s s₁ s₂ : ω.substance}
   
 lemma subset_of_subsist : e₁.subsists e₂ → e₁.exist ⊆ e₂.exist :=
  begin
      intros h w hw,
      simp [entity.subsists] at h,
      rw <-h,
      simp [hw],
  end
 
 lemma sub_of_inheres : a.inheres s → a.val.exist ⊆ s.val.exist := 
    by simp [accident.inheres]; exact subset_of_subsist a.val s.val
   

 
 -- An entity is a substance if and only if it subsists in itself.
 lemma self_subsist : perfect e ↔ (e.subsists e) :=
  begin
      constructor; intro h,
          ext, constructor; intro h₂,
              cases h₂,
                  exact h₂,
              simp [event.exterior, interior_compl] at h₂,
              simp [perfect, event.dense] at h,
              rw h at h₂,
              simp at h₂,
              contradiction,
          simp [h₂],
      apply sub_support,
      existsi e,
      exact h,
  end
 
  
 @[simp]
 lemma inheres_owner : a.inheres a.owner :=
      by simp [accident.inheres, accident.owner, entity.subsists]
  
 lemma unique_inheres : a.inheres s₁ → a.inheres s₂ → s₁ = s₂ :=
  begin
      intros h₁ h₂,
      obtain ⟨⟨s₁, op₁, ne₁⟩, pe₁⟩ := s₁,
      obtain ⟨⟨s₂, op₂, ne₂⟩, pe₂⟩ := s₂,
      simp [accident.inheres, entity.subsists] at *,
      rwa h₁ at h₂,
  end
 

end subsistence_lemmas

-- We delve a little deeper in our definitions concerning accidents.
section accidents

 -- An entity is called `simple` if it has no accidents.
 @[reducible]
 def simple (e : ω.entity) := e.subsistents = ∅
 @[reducible]
 def composite (e : ω.entity) := ¬ simple e

  -- regular accidents are called intrinsic
  -- and irregular accidents are called extrinsic
  @[reducible]
  def intrinsic (a : ω.accident) := a.val.exist.regular
  @[reducible]
  def extrinsic (a : ω.accident) := ¬ a.val.exist.regular

  -- A connected intrinsic accident is called a quality
  structure quality (ω : ontology) :=
    (exist : ω.event)
    (is_open : is_open exist)
    (ne : exist.nonempty)
    (imperfect : ¬ exist.dense)
    (intrinsic : exist.regular)
    (connected : is_preconnected exist)
 
  def quality.entity (q : ω.quality) : ω.entity := ⟨q.exist, q.is_open, q.ne⟩
  def quality.acc (q : ω.quality) : ω.accident := ⟨q.entity, q.imperfect⟩

  -- a disconnected intrinsic accident is a quantity
 --   structure quantity :=
 --     (acc : accident)
 --     (intrinsic : intrinsic acc)
 --     (is_disconnected : ¬ is_preconnected acc.val.exist)

end accidents

-- And prove lemmas about them
section accident_lemmas

 -- All accidents are simple
 lemma acc_simp :  ∀ a : ω.accident, simple a.val := 
  begin
      intro a,
      simp [simple],
      dunfold entity.subsistents,
      ext, constructor; intro h; simp at *,
          have c₀ : perfect a.val,
              apply sub_support,
              existsi x,
              exact h,
          have c₁ : ¬ perfect a.val := a.property,
          contradiction,
      contradiction,
  end

 -- Nonempty finite intersections of accidents are accidents
 def accident.inter (a₁ a₂ : ω.accident) (h : a₁.val.compatible a₂.val) : ω.accident :=
  begin
      fsplit,
          exact a₁.val.inter a₂.val h,
      simp [set_of, imperfect],
      intro h₂,
      set α := a₁.val.inter a₂.val h,
      have c₁ : α.exist ⊆ a₁.val.exist,
          simp [α],
          dunfold entity.inter,
          simp,
      let β : ω.substance := ⟨α, h₂⟩,
      have c₂ := @substance_of_substance_entails _ β a₁.val c₁,
      exact absurd c₂ a₁.property,
  end


 lemma exterior_of_accident_is_accident : ∀ {a : ω.accident}, 
                                           is_open a.val.exist.exterior ∧
                                           a.val.exist.exterior.nonempty ∧
                                           ¬ a.val.exist.exterior.dense
                                           :=
    begin
        intros a,
        admit,
        -- constructor,
        --     simp [event.exterior],
        --     dunfold event.dense,
        --     dunfold event.exterior,
        -- split, admit,
        -- split, admit,
        -- admit,
    end
  
 def accident.exterior (a : ω.accident) : ω.accident := 
    ⟨⟨a.val.exist.exterior, exterior_of_accident_is_accident.1, exterior_of_accident_is_accident.2.1⟩,exterior_of_accident_is_accident.2.2⟩  

 lemma aux : ∀ (s : ω.substance) (q : ω.quality) 
              (S : set (subtype s.val.exist)),
              is_open S →
              is_connected S → 
              q.exist ⊆ subtype.val '' S →
              q.acc.inheres s →
              subtype.val '' S = q.exist :=
    begin
        intros s q S is_openS is_connectedS h₁ h₂,
        simp [set.image, subtype.val],
        ext, constructor; intros h; simp at *,
            obtain ⟨h, elem⟩ := h,
            have c : x ∈ q.exist ∪ q.exist.exterior,
                simp [accident.inheres, entity.subsists] at h₂,
                revert h₂,
                dunfold quality.acc quality.entity,
                -- simp,
                intro h₂,
                rw h₂,
                exact h,
            cases c,
                assumption,
            have c₁ : q.exist.exterior ⊆ s.val.exist,
            repeat{admit},
                -- apply subset_of_subsist q.entity s.val,
            -- revert w,
            -- simp [is_preconnected] at hs₁,
    end

end accident_lemmas
 
 
 -- section universals
 
 --  -- We can define virtual substances as products, 
 --  -- coproducts, subtypes and quotients of 
 --  -- state spaces of real substances.
 --  -- These spaces so generated represent the would be state spaces
 --  -- of entities which perhaps are not possible to exist.
 
 --  -- Concepts are virtual substances abstracted away from the state
 --  -- spaces of particulars substances. 
 --  -- Universals are concepts defined up to isomorphism.
 
 --  -- The process of abstraction, telling whether a Type has been
 --  -- abstracted away from particular substances.
 --  -- An element of this type is one possible way the topological
 --  -- space could be abstracted from the particulars, i.e.
 --  -- it is an abstraction of the space.
 --  class inductive abstraction : Π (α : Type u) [topological_space α], Type (u+1)
 --   | particular (s : substance) : abstraction s.state
 --   | pi           {I : Type u} (get : I → Type u)
 --                  [get_top : Π i : I, topological_space (get i)]
 --                  (h : ∀ i : I, abstraction (get i) ) 
 --                  : abstraction (Π i : I, (get i))
  
 --   | sigma        {I : Type u} (get : I → Type u)
 --                  [get_top : Π i : I, topological_space (get i)]
 --                  (h : ∀ i : I, abstraction (get i) ) 
 --                  : abstraction (Σ i : I, (get i))
   
 --   | subtype      {α : Type u} [topological_space α]
 --                  (p : α → Prop)
 --                  (h : abstraction α)
 --                  : abstraction (subtype p)
   
 --   | quotient     {α : Type u} [topological_space α]
 --                  (s : setoid α)
 --                  (h : abstraction α)
 --                  : abstraction (quotient s)
 
 --  instance particular (s : substance) : abstraction s.state := abstraction.particular s 
 
 --  -- CONCEPTS
 
 --   -- A concept for a Type is a topology
 --   -- for that Type that was abstracted away
 --   -- from the particular substances.
 --   -- It is a "concrete universal", an
 --   -- universal not defined up to isomorphism.
 --   inductive concept : Type (u+1)
 --   | mk   (state : Type u)
 --          [t : topological_space state]
 --          [abs : abstraction state]
 --          : concept
 
 --   def substance.concept (s : substance) : concept := ⟨s.state⟩
  
 --   def concept.state (c : concept) : Type u :=
 --     by obtain ⟨state, _, _⟩ := c; exact state
 
 --   instance concept.t (c : concept) : topological_space c.state := 
 --     by obtain ⟨_, t, _⟩ := c; exact t
  
 --   instance concept.abs (c : concept) : abstraction c.state := 
 --     by obtain ⟨_, _, abs⟩ := c; exact abs
 
 --   -- concepts are inhabited by the concept of a
 --   -- necessary being.
 --   instance concept_inhabited : inhabited concept := ⟨nb.concept⟩
  
 --   variable c : concept
  
 --   @[reducible]
 --   def concept.event := set c.state
   
 --   -- Concepts can have world indexed states just as substances
 --   -- but the concept doesnt just make sense for just any concept,
 --   -- so occasionally we can associate a nonempty set of states to
 --   -- a concept and occasionally it will be empty 
 --   -- (namely, if the concept is defined as a subconcept of another concept).
 --   def concept.state_at (w : world) : c.event :=
 --     begin
 --         cases c,
 --         induction c_abs,
 --             exact {c_abs.state_at w},
 --         all_goals {
 --             dunfold concept.event concept.state,
 --             simp,
 --         },
 --         repeat {
 --             have ih : Π (i : c_abs_I), set (c_abs_get i) := c_abs_ih,
 --             intro x,
 --         },
 --         exact ∀i, x i ∈ ih i,
 --         exact x.snd ∈ ih x.fst,
 --         exact {x | x.val ∈ c_abs_ih},
 --         exact (@quotient.mk _ c_abs_s) '' c_abs_ih,
 --     end
   
 --   -- Given this we can define the notion of
 --  -- a map between state spaces preserving states.
 --  def state_preserving {c₁ c₂ : concept} (f : c₁.state → c₂.state) :=
 --     ∀ w, f '' (c₁.state_at w) ⊆ c₂.state_at w
  
 --   -- An abstract quality is the analogue for concepts
 --   -- of the perfections of substances.
 --   structure concept.quality :=
 --     (exist : c.event)
 --     (is_open : is_open exist)
 --     (ne : exist.nonempty)
 --     (nuniv : exist ≠ univ)
 
 --   -- check whether an event is a quality
 --   def concept.is_quality (e : c.event):= is_open e ∧ e.nonempty ∧ e ≠ univ
  
 --   -- We can generate the set of substances which grounds a concept
 --   -- in reality. That is the set of substances from which the concept
 --   -- was abstracted.
 --   def concept.grounded (c : concept) : set substance :=
 --     begin
 --         cases c,
 --         induction c_abs,
 --             exact {c_abs},
 --             repeat{exact ⋃ i, c_abs_ih i},
 --             repeat{assumption},
 --     end
 
 --   -- Given a set of substances it is possible to
 --   -- construct different types of wholes/totalities
 --   -- which contain the set
 --   def integral_whole (s : set substance) : concept :=
 --   let get := λx : subtype s, x.val.state,
 --       type := Π i : subtype s, (get i)
 --   in begin
 --     set abs := abstraction.pi get (by apply_instance),
 --     exact @concept.mk type _ abs,
 --   end
 
 --   def abstract_whole (s : set substance) : concept :=
 --   let get := λx : subtype s, x.val.state,
 --       type := Σ i : subtype s, (get i)
 --   in begin
 --     set abs := abstraction.sigma get (by apply_instance),
 --     exact @concept.mk type _ abs,
 --   end 
 
 --  -- UNIVERSALS
 
 --   -- Since universals will 
 --   -- be equivalence classes of concepts, 
 --   -- we need to define a setoid of concepts.
 
 --   -- Two concepts are equivalent if they are homeomorphic
 --   @[reducible]
 --   def concept_equiv (c₁ c₂ : concept) :=
 --     nonempty (c₁.state ≃ₜ c₂.state)
 
 --   instance concept_setoid : setoid concept :=
 --   begin
 --     fconstructor,
 --         exact concept_equiv,
 --     repeat{constructor};
 --     simp [reflexive, symmetric, transitive],
 --         intro x,
 --         exact ⟨homeomorph.refl x.state⟩,
 --     intros x y h,
 --     constructor,
 --     exact homeomorph.symm h,
 --         intros x y z h₁ h₂,
 --         constructor,
 --         exact homeomorph.trans h₁ h₂,
 --   end
   
 --   -- finally
 --   def universal := quotient concept_setoid
  
 --   -- In order to the define the concept of `essence` and that of
 --   -- `definition` we require the definition of an invariant property.
 --   @[reducible]
 --   def property := concept → Prop
 --   def property.invariant (p : property) :=
 --     ∀ c₁ c₂ : concept, 
 --     c₁ ≈ c₂ → (p c₁ ↔ p c₂)
 
 --   -- The essence of an universal is a property which defines
 --   -- its concepts up to homeomorphism.
 --   def universal.is_essence (u : universal) (p : property) :=
 --     p.invariant ∧
 --     ∃ c₁, ⟦c₁⟧ = u ∧ p c₁ ∧
 --     (∀ c₂, p c₂ → c₁ ≈ c₂)
 
 --   @[reducible]
 --   def universal.essence (u : universal) := subtype u.is_essence
  
 --   -- every universal has an essence
 --   theorem essentialism : ∀ u : universal, nonempty u.essence :=
 --     begin
 --         intro u,
 --         -- Take a representative concept c,
 --         -- then equivalence with c is the essence of u.
 --         -- Do note however that this essence is noncomputable,
 --         -- because u.out depends on classical.choice.
 --         -- So even though we know that every universal has an
 --         -- essence we do not know (in more concrete terms)
 --         -- the essence of every universal.
 --         -- Now, if instead we defined this in terms of concepts we
 --         -- would be able to construct the essence, therefore it makes
 --         -- more sense philosophically to only define essence for universals.
 --         let c := u.out,
 --         repeat{fconstructor},
 --             exact (≈) c,
 --             simp [property.invariant],
 --                 suffices h : ∀ (c₁ c₂ : concept), c₁ ≈ c₂ → (c ≈ c₁ → c ≈ c₂),
 --                     intros c₁ c₂ h₂,
 --                     have h₃ : c₂ ≈ c₁ := setoid.symm h₂,
 --                     exact ⟨h c₁ c₂ h₂, h c₂ c₁ h₃⟩,
 --                 intros c₁ c₂ h₁ h₂,
 --                 exact setoid.trans h₂ h₁,
 --             exact c,
 --             simp [c],
 --             simp,
 --     end
 
 
 --   -- In another sense u.out, for u an universal, might be considered to be
 --   -- the essence of u, since it is an "abstract" representative of u.
 --   -- In this sense we could consider (e.g.) "the" natural numbers 
 --   -- to be an "essence" of sorts, because given the class of all models of
 --   -- second order arithmetic, neither a particular model nor the class itself
 --   -- appears to be a good candidate for "the" natural numbers, but an abstract
 --   -- representative of the class appears to be it. In this sense we can
 --   -- somewhat avoid the "up to isomorphism" restriction placed upon mathematical
 --   -- concepts. A restriction which, if we were to be consistent with it, should
 --   -- preclude us from talking about "the" natural numbers at all.
  
 --   -- It appears to be the same thing for most purposes to either take
 --   -- u.out as the essence or the relation of "being homeomorphic to u.out"
 --   -- as the essence. Although it would look like the first point of view
 --   -- is the traditional essentialist one, while the second appears to be
 --   -- some form of similarity nominalism. Arguably even this similarity 
 --   -- view is a pretty essentialistic one insofar as the representative u.out
 --   -- is totally abstract and impossible to concretely construct or to.
 --   -- concretely compare with anything except by means of essential invariant
 --   -- properties which are necessarilly true for all instances of an universal.
  
 --   -- In this the noncomputable nature of classical.choice can be given 
 --   -- a philosophical interpretation, since we cannot compute or construct
 --   -- abstract essences, otherwise they would be concrete.
  
 --   -- The representation u.out also acts as a generic instance of the universal.
 --   -- For any given invariant property, suffices to show that it is valid
 --   -- for u.out to conclude it is valid for any representation.
 --   -- An example of this is given below:
  
 --   -- A concept is instantiable if it is homeomorphic to the state
 --   -- space of a substance, so that it could be thought as being an
 --   -- entity of the same species as that substance.
 --   def concept.instantiable : property := λc, ∃ s : substance, s.concept ≈ c
  
 --   -- Instantiability is of course an invariant
 --   lemma concept_instantiable_invariant : concept.instantiable.invariant :=
 --     begin
 --         dunfold concept.instantiable property.invariant,
 --         intros c₁ c₂ h,
 --         suffices c : (∃ (s : substance), substance.concept s ≈ c₁) → ∃ (s : substance), substance.concept s ≈ c₂,
 --             constructor,
 --                 exact c,
 --             all_goals{
 --                 intro hs,
 --                 obtain ⟨s, hs⟩ := hs,
 --                 existsi s,
 --             },
 --             exact setoid.trans hs (setoid.symm h),
 --         exact setoid.trans hs h,
 --     end
 
 --   -- Therefore we define instantiablity for universals via quotient.out
 --   def universal.instantiable (u : universal) := u.out.instantiable
  
 --   -- TODO: argue that Aquinas defended the u.out point of view in
 --   -- De ente et essentia.
  
 --   -- The nb as an universal.
 --   @[reducible]
 --   def nbu : universal := ⟦nb.concept⟧
 --   instance universal_inhabited : inhabited universal := ⟨nbu⟩
  
 --   -- A notion is a quality defined abstractly in the representation
 --   def universal.notion (u : universal) := u.out.quality 
 
 
 --  end universals
 -- section categories
  
 --  -- A definition of the 10 Aristotelian Categories,
 --  -- and of the subcategories Aristotle mentions in his work.
 --  -- The Categories of Substance and Quality were already defined.
 
 --  variable c : concept
 
 --  -- A quantity for a concept is a continuous
 --  -- map from states of the concept to the reals.
 --  def concept.quantity := subtype {f : c.state → ℝ | continuous f }
 
 --  --  We couldn't find the definition of a probability measure in mathlib.
 --  instance concept.borel : measurable_space c.state := borel c.state
 --  def concept.probability_measure := {μ : measure_theory.measure c.state | μ.measure_of univ = 1} 
 
 --  -- A disposition is a partly state-indexed probability measure for a concept
 --  -- such that the preimage of every probability measure is either open or closed.
 --  def concept.disposition := 
 --     subtype {f : c.state →. c.probability_measure | ∀ p : c.probability_measure, is_open (f⁻¹' {roption.some p}) ∨ is_closed (f⁻¹' {roption.some p})}
 
 --  -- A habit is a "permanent" disposition. We take this to mean that
 --  -- it is constant in a dense open set.
 --  def concept.habit := 
 --     subtype {d : c.disposition | ∃ p : c.probability_measure,  closure (d.val⁻¹' {roption.some p}) = univ}
 
 --  -- a law of nature is a constant disposition, i.e. the same for every
 --  -- state. It is provably a habit as well. 
 --  -- The usual talks of "laws of nature" are laws of nature in the "cosmos"
 --  -- (to be defined later), assuming that these laws are necessary. But if
 --  -- they are contingent they are assumed to be habits.
 
 --  def concept.law := 
 --     subtype {d : c.disposition | ∃ p : c.probability_measure, ∀ x : c.state, p ∈ d.val x}
 
 
 --  end categories
 -- section matter
 
 --  -- We call any composite substance `physical`,
 --  -- or a `body`.
  
 --  @[reducible]
 --  def physical (s : substance) := composite s.val
 --  def cosmos_set := {s : substance | physical s}
 --  def body := subtype cosmos_set
  
 --  -- The cosmos is the integral whole of all
 --  -- composite (physical) substances.
 --  def cosmos := integral_whole cosmos_set
 
 --  -- Prime matter is the abstract whole of all
 --  -- composite (physical) substances.
 --  def prime_matter := abstract_whole cosmos_set
  
 --  -- There are specifically two dual notions of `matter` that are obtained 
 --  -- by considering virtual substances (concepts) 
 --  -- as the totalities of both kinds of matter:
  
 --  -- (1) From the point of view of the whole, 
 --  -- matter can be thought of as that which 
 --  -- actively composes a thing, its substratum.
 --  -- This sense we will only cover in the next
 --  -- section, which is mereology.
  
 --  -- (2) From the point of view of matter itself,
 --  -- matter can be thought of as that which is in potency
 --  -- to a multiplicty of forms, in the sense of prime matter.
 --  -- Mathematically these two notions are dual, 
 --  -- with the duality of Π and Σ types, respectively.
 
 --  -- Notice, in the first notion matter is actual, 
 --  -- and in the second potential.
  
 --  -- Transcendent matter is the abstract whole of all
 --  -- substances.
 --  -- This is the virtual substance that is "in potency"
 --  -- for becoming any other substance.
 --  def transcendent_matter : concept := abstract_whole univ
 
 --  -- The state space of a virtual, likely possible, substance
 --  -- corresponding to a concrete and immanent notion of matter.
 --  -- This virtual is the mereological sum of the set of all substances.
 --  -- It is the whole of reality.
 --  def reality : concept := integral_whole univ
 
 --  -- Of course nothing in reality is an instance of
 --  -- prime or transcendent matter.
 
 --  end matter
 -- section mereology
 
 --  -- A substance s₁ is an integral part of another
 --  -- substance s₂ if there is a 
 --  -- (necessarilly nonempty) set S of substances 
 --  -- such that the integral whole of {s₁} ∪ S is
 --  -- homeomorphic to the state space of s₂ by
 --  -- means of a state-preserving homeomorphism
 --  def substance.part_of (s₁ s₂ : substance) :=
 --     -- s₁ ≠ s₂ ∧
 --     ∃ S : set substance, 
 --     S.nonempty ∧
 --     s₁ ∉ S ∧
 --     -- (∀ x ∈ S, x ≠ s₂) ∧
 --     ∃ hom :
 --         s₂.concept.state ≃ₜ
 --         (integral_whole $ S ∪ {s₁}).state,
 --     state_preserving hom.to_fun
 
 --  -- This is to say that if we know the state of the
 --  -- substance s₂ in a possible world w, then we
 --  -- already know the state of each of its parts,
 --  -- since there is a functional dependence between them.
 
 
 --  --  lemma
  
 --  --  @[trans]
 --  --  lemma part_of_trans : ∀ s₁ s₂ s₃ : substance, 
 --  --                        s₁.part_of s₂ →
 --  --                        s₂.part_of s₃ →
 --  --                        s₁.part_of s₃ :=
 --  --     begin
 --  --         intros s₁ s₂ s₃ h₁ h₂,
 --  --         -- simp [substance.part_of] at *,
 --  --         obtain ⟨S₁, ne₁, notin₁, hom₁, h₁⟩ := h₁,
 --  --         obtain ⟨S₂, ne₂, notin₂, hom₂, h₂⟩ := h₂,
 --  --         use S₁ ∪ S₂ ∪ {s₂},
 --  --     end
 
 --  end mereology
 -- section causality
 
 --  def counterfactual_dependence (w : world) (e₁ e₂ : entity) : Prop := sorry
 
 --  end causality
 -- section metaphysics
 
 --  -- We call a substance `metaphysical`, or a `separate substance`, if it is simple.
 --  -- It is otherwise `physical`, or a `body`, as already mentioned.
 --  @[reducible]
 --  def metaphysical (s : substance) := simple s.val
 --  def separate := subtype {s : substance | metaphysical s}
  
 --  -- A substance is purely actual if it has no passive potency
 --  -- to be different from what it is, i.e. if it has a single state.
 --  def purely_actual (s : substance) := nonempty (s.state ≃ unit)
  
 --  -- Only the necessary being can be purely actual, 
 --  -- in which case platonism follows.
 --  -- def eq_nb_of_purely_actual : ∀ s, purely_actual s → s = nb :=
 --  -- begin
 --  --     intros s h,
 --  --     simp [purely_actual] at h,
 --  --     apply nonempty.elim h,
 --  --     intro iso,
 --  --     simp [substance.state, substance.state_setoid, quotient] at iso,
      
 --  -- end
  
 --  -- Platonism in the broad sense (greek theism) is the doctrine 
 --  -- that the necessary being is metaphysical
 --  def platonism := metaphysical nb
  
 --  -- The admission of any metaphysical substance entails platonism
 --  lemma platonism_of_nonempty_separate : nonempty separate → platonism :=
 --  sorry
 --  end metaphysics
 -- section theology
  
 --  -- (Classical) Theism is an extension of Platonism which 
 --  -- furthermore claims that there is a possible world 
 --  -- in which the necessary being exists alone.
 --  def theism := platonism ∧ ∃ (w : world), world.entities w = {nb.val}
  
 --  end theology
 -- section ethics
  --  end ethics

end ontology
