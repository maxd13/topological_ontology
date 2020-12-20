import alexandroff_space
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


-/

-- An `ontology` is a nonempty T0 topological space
-- of possible worlds.
class ontology :=
    (world : Type*)
    [wne : nonempty world . tactic.apply_instance]
    [t : topological_space world . tactic.apply_instance]
    -- identity of indiscernibles for possible worlds
    [axiom₀ : t0_space world . tactic.apply_instance]


instance ontology_top  (ω : ontology)  : topological_space ω.world := ω.t
instance ontology_ne  (ω : ontology)  : nonempty ω.world := ω.wne
instance ontology_t0  (ω : ontology)  : t0_space ω.world := ω.axiom₀

-- Events in an ontology are simply sets of worlds.
-- Events (informally) are said to `occur` precisely in their element worlds.
@[reducible, alias]
def ontology.event (ω : ontology) := set ω.world 

-- intensional ontologies
structure iontology extends ontology :=
    (entity : Type*)
    [ene : nonempty entity . tactic.apply_instance]
    (map : entity → to_ontology.event)
    (axiom₁ : t = (generate_from $ range map))

-- (algebraic) realism for intensional ontologies
class iontology.realist (Ω : iontology) : Prop :=
    (postulate₀ : Ω.t.is_open = (range Ω.map))

namespace ontology

section ontology
 
 variable (ω : ontology)

 -- However the least we should assume for an ontology to be worthy of consideration as being
 -- the true ontology is that we can add or remove entities from its worlds, therefore, we add
 -- the following definitions:
 
 class viable : Prop :=
     (postulate₁ : ∀ w : ω.world, ∃ w', w < w' ∨ w' < w)
 
 -- common (sensical) ontologies
 class common extends viable ω : Prop :=
     (postulate₂ : uncountable ω.world)
 
 def alexandroff_discrete := alexandroff_space ω.world
 
 class alexandroff extends common ω:=
     (postulate₃ : alexandroff_discrete ω)

--  -- ω is generated by the intensional map.
-- class ontology.intensional (ω : ontology) (f : intensional_map) : Prop :=
--     (intensional : ∃ h : f.world = ω.world, 
--                     let t := f.top
--                     in by rw h at t; exact t = ω.t
--     )

-- -- ω is an extensional interpretation of a pre-existing ontology
-- class ontology.intensionalizable (ω : ontology) (intensional_entities : Type*) : Prop:=
--     ( intensionalizable : ∃ f : intensional_map, 
--       f.entity = intensional_entities ∧ 
--       ω.intensional f
--     ) 

end ontology

variable {ω : ontology}

-- We introduce first the notion of events. 
section events
 
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
 def event.frontier := frontier e

 -- necessity and contingency
 def event.contingent := e ≠ univ
 def event.necessary := e = univ
  
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
       have c := ω.wne,
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
 
 -- An entity is `contingent` if it is not the necessary being.
 def entity.contingent := e ≠ ω.nbe
 -- And otherwise necessary
 def entity.necessary := e = ω.nbe

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
 def entity.perfect (e : ω.entity) := e.exist.dense
 @[reducible]
 def entity.imperfect (e : ω.entity) := ¬ e.perfect
 def substance (ω : ontology) := subtype {e : ω.entity | e.perfect}
 def accident (ω : ontology) := subtype {e : ω.entity | e.imperfect}
 
 -- By this definition, it is obvious that any entity 
 -- is either a substance or an accident, therefore we can
 -- cast it to one of them.
 
 -- antepredicament of an entity
 noncomputable def entity.ante (e : ω.entity) : ω.substance ⊕ ω.accident :=
  begin
      by_cases e.perfect,
          left,
          exact ⟨e, h⟩,
      right,
      exact ⟨e, h⟩,
  end

 -- The `necessary being` is the substance that exists in every possible world.
 def nb (ω : ontology) : ω.substance := 
       ⟨ω.nbe, by simp [nbe, set_of, entity.perfect, event.dense]⟩
   
 instance substance.inhabited : inhabited ω.substance := ⟨ω.nb⟩
 
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

 lemma perfect_iff_nocontrary : ∀ e : ω.entity, e.nocontrary ↔ e.perfect :=
     begin
        intro e,
        constructor; intro h,
            simp [entity.perfect, event.dense],
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
                                           s.val ⊆ e → e.perfect :=
    begin
        intros s e h,
        simp [entity.perfect, event.dense],
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
      simp [set_of, entity.perfect, event.dense, entity_Sup],
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
      simp [set_of, entity.perfect, event.dense],
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
 lemma sub_support :  ∀ {e}, (∃x : ω.entity, x.subsists e) → e.perfect :=
  begin
      intros e h,
      obtain ⟨y, h⟩ := h,
      simp [entity.perfect, event.dense],
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

 -- entity cast to a substance if perfect, or the owner of the accident if imperfect.
 noncomputable def entity.substance (e : ω.entity) : ω.substance :=
    match entity.ante e with
    | (sum.inl val) := val
    | (sum.inr val) := val.owner
    end


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
 lemma self_subsist : e.perfect ↔ (e.subsists e) :=
  begin
      constructor; intro h,
          ext, constructor; intro h₂,
              cases h₂,
                  exact h₂,
              simp [event.exterior, interior_compl] at h₂,
              simp [entity.perfect, event.dense] at h,
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
 def simple (e : ω.entity) := ∀ e' : ω.entity, e'.subsists e → e' = e 
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
--  lemma acc_simp :  ∀ a : ω.accident, simple a.val := 
--   begin
--       intro a,
--       simp [simple],
--     --   intros e 
--       ext, constructor; intro h; simp at *,
--           have c₀ : a.val.perfect,
--               apply sub_support,
--               existsi x,
--               exact h,
--           have c₁ : ¬ a.val.perfect := a.property,
--           contradiction,
--       contradiction,
--   end

 -- Nonempty finite intersections of accidents are accidents
 def accident.inter (a₁ a₂ : ω.accident) (h : a₁.val.compatible a₂.val) : ω.accident :=
  begin
      fsplit,
          exact a₁.val.inter a₂.val h,
      simp [set_of, entity.imperfect],
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

-- We now talk about analogical (fuzzy) events, or "avents".
-- OBSERVATION: We could have called them aevents, which would be in keeping with our naming style.
-- But then since in Latin this just sounds like "events" we preferred to invent a new word.
section avents

-- [0, 1] interval
def I := Icc (0 : ℝ) 1

@[reducible, alias]
def avent (ω : ontology) :=  ω.world → I 

end avents

-- Next we must talk about properties
section properties

-- A property is a function which outputs an event for an entity, 
-- i.e. the event of the entity having the property.
@[reducible, alias]
def property (ω : ontology) :=  ω.entity → ω.event

-- An analogical property, or aproperty, outputs an avent instead.
-- i.e the avent of the entity having the property, which it can posses to a greater or lesser extent.
-- This is analogy in the sense of intrinsic attribution.
@[reducible, alias]
def aproperty (ω : ontology) := ω.entity → ω.avent

variable (p : ω.property)

-- Apparently Lean already infers correctly the proper notation for this (which is amazing),
-- even though it does not elaborate the full boolean algebra instance.
-- instance boolean_property : boolean_algebra ω.property := sorry

/-! Now, a property which, unlike an aproperty, does not return an avent is in some sense univocal,
 but this univocity might occur in two different ways: in language alone, or both in language and in reality.
 The latter we call univocal properties properly speaking, while the former we call *hidden* or *abstracted* 
 analogical properties. The difference between these two is that real univocal properties preserve hierarchical
 distinctions in being, while abstracted, "fake", univocal properties ignore such ontological distinctions.
 So essentially we say that a property is univocal in a possible world if and only if the entities which exemplify 
 it in that world are incomparable with respect to existential entailment.
-/

-- TODO: change this definition to use existential entailment notation when it becomes available.
def property.lunivocal : ω.event := 
    { w |
      ∀ e₁ e₂, w ∈ p e₁ ∩ p e₂ → ¬ e₁.exist ⊂ e₂.exist ∧ ¬ e₁.exist ⊃ e₂.exist
    }
@[reducible]
def property.lhidden := -p.lunivocal
@[reducible]
def property.univocal := p.lunivocal.necessary
@[reducible]
def property.hidden := p.lhidden.necessary

/- The whole point of the Thomistic theory of the analogy of being consists 
   in the realization that existence is a hidden analogy abstracted away from a deeper
   aproperty: Being.
-/

def existence (ω : ontology) : ω.property := λe, e.exist

-- In any possible world with at least 2 entities (hence at least one contingent entity) 
-- existence is a hidden analogy.
theorem analogical_existence : ∀ w e₁ e₂, e₁ ≠ e₂ → e₁ ∈ w → e₂ ∈ w → w ∈ ω.existence.lhidden := sorry

instance property_inhabited : inhabited ω.property := ⟨ω.existence⟩


-- a property is exemplifiable if there is some entity which has that property in some possible world.
@[reducible]
def property.exemplifiable  : Prop := ∃ e, (p e).nonempty

-- an entity is said to possibly exemplify a property if it does so in some possible world
@[reducible]
def entity.pexemplifies (e : ω.entity) := (p e).nonempty 

-- a property is existential if an entity having the property implies its existence
@[reducible]
def property.existential := ∀ e, p e ⊆ e.exist

-- the common (sensical) properties
structure property.common : Prop :=
    (axiom₀ : p.exemplifiable)
    (axiom₁ : p.existential)

-- A common property is positive if in any possible world in which an entity has the property,
-- there exists something in that world (e.g. an accident) to ground the property.
structure property.positive extends property.common p : Prop := 
    (axiom₂ : ∀ e, is_open (p e))

-- a property is essential of an entity if the entity has that property in any and only the possible worlds
-- in which it exists. Which is to say that the entity is in a sense a "fixed point" of the property
@[reducible]
def property.essential_of (e : ω.entity) := p e = e.exist
@[reducible]
def property.inessential_of (e : ω.entity) := p e ≠ e.exist

-- a property is essential in itself if it is essential of all entities which may possibly exemplify it.
@[reducible]
def property.essential := ∀ e, (p e).nonempty → p.essential_of e
-- It is inessential in itself if it is everywhere inessential
@[reducible]
def property.inessential := ∀ e, (p e).nonempty → p.inessential_of e

-- a positive property is possessed if it "talks about" its subject,
-- which is to say that it is an accident or essential of a substance,
-- or essential of an accident.
structure property.possessed extends property.positive p : Prop  :=
    (axiom₃ : ∀ (e : ω.entity) (h : e.pexemplifies p), 
              let r := (entity.mk (p e) (axiom₂ e) h) in
              e.perfect → r.subsists e
    )
    (axiom₄ : ∀ (e : ω.entity), e.pexemplifies p → e.imperfect → p.essential_of e)

-- A possessed property is accidental of an entity if it is not essential.
-- From this we can infer (informally) that a property is either essential or accidental
-- of an entity or does not "talk about" an entity at all 
-- (or at least does not "talk about" all entities to which it is predicated).
@[reducible]
def property.accidental_of (e : ω.entity) := p.possessed ∧ p.inessential_of e
@[reducible]
def property.accidental := p.possessed ∧ p.inessential

-- Notice there can be possessed properties which are neither essential nor accidental in themselves,
-- but only with respect to a particular entity (it is in this sense that some say heat is
-- essential of fire but accidental of burning coal). But with respect to any particular entity
-- a possessed property is either essential or accidental. Notice also that this sort of property
-- is (almost) never univocal, because predicating something of both a substance and its accidents is never univocal.

-- a "proper" property, or a property in a more "proper" sense of the word,
-- is an univocal possessed property 
structure property.proper extends property.possessed p : Prop :=
    (axiom₅ : p.univocal)

-- The haecceity of an entity is an essential proper property from which all its essential properties
-- follow.
variable (e : ω.entity)

def entity.haecceity  : ω.property := λx w, x ∈ w ∧ x = e

theorem haecceity_essential : e.haecceity.essential := sorry
theorem haecceity_proper : e.haecceity.proper := sorry
theorem haecceity_follows_essential : p.essential_of e → e.haecceity ≤ p  := sorry

-- a property is communicable if it can be possibly exemplified by more than one entity
def property.communicable := ∃ e₁ e₂ : ω.entity,
                             e₁ ≠ e₂ ∧
                             e₁.pexemplifies p ∧
                             e₂.pexemplifies p

def property.incommunicable := ¬ p.communicable

-- haecceity is of course incommunicable
lemma haecceity_incommunicable : e.haecceity.incommunicable := sorry

-- A normal, "everyday", property like "being red" 
-- (when e.g. it is predicated of substances, and not of "red" accidents)
-- is a communicable proper property.
structure property.normal extends property.proper p : Prop :=
    (axiom₆ : p.communicable)


-- Don't know if this is true
-- there are counterexamples when S contains contradictory properties
-- but otherwise maybe an adaptation of this lemma is true
-- lemma inf_normal_normal : ∀ S : set ω.property, (∀ p : ω.property, p ∈ S → p.normal) → (Inf S).normal :=
--     begin
--         intros S h,
--         have ne : S.nonempty,
--             admit,
--         obtain ⟨p, hp⟩ := ne,
--         have pn := h p hp,
--         constructor,
--             admit,
--         obtain ⟨e₁,e₂,neq, he₁,he₂⟩  := pn.axiom₆,
--     end


-- The specific essence, or species, of an entity is a normal essencial property from which
-- all its normal essential properties follow.
def property.species_of := e.pexemplifies p ∧
                           p.normal ∧ 
                           p.essential ∧
                           ∀ p', e.pexemplifies p' → 
                                p'.normal →  
                                p'.essential →
                                p ≤ p'

def property.species := ∃ e, p.species_of e
def entity.has_species := ∃ p : ω.property, p.species_of e

-- An entity has at most one species
lemma unique_species : ∀ p₁ p₂ : ω.property, (∃ e, p₁.species_of e ∧ p₂.species_of e) → p₁ = p₂ := sorry

end properties

-- weakly substantially finitistic ontologies
def wsfinitistic (ω : ontology) : Prop := ∃ w : ω.world, finite {s : ω.substance | s.val ∈ w}

end ontology

