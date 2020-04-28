import 
    topology.bases
    topology.order 
    topology.homeomorph
    topology.subset_properties
    data.real.basic
    topology.instances.real
    measure_theory.borel_space
    measure_theory.measure_space
    tactic.tidy
universe u
open set topological_space classical
local attribute [instance] prop_decidable

namespace ontology
section ontology
-- An `ontology` is an inhabited T0 topological space
-- of possible worlds.
parameters {world : Type u}
           [t : topological_space world]
           [ne : inhabited world]
           [axiom₀ : t0_space world]


-- The default world is the actual world.
-- We introduce a notation for it.
local notation `ω₀` := default world

-- Events in an ontology are simply sets of worlds.
@[reducible, alias]
def event := set world

include t ne axiom₀

section particulars
 
 -- EVENTS
  
  -- An event (informally) `occurs` precisely in the worlds it contains,
  -- and it `obtains` if it occurs in the actual world.
  @[reducible]
  def event.obtains (e : event) := ω₀ ∈ e
  
  -- We define the related topological notions for events.
  -- @[reducible]
  -- def event.interior (e : event) := interior e
  -- @[reducible]
  -- def event.closure  (e : event) := closure e
  @[reducible]
  def event.dense (e : event) := closure e = univ
  @[reducible]
  def event.exterior (e : event) : event := interior (-e)
  @[reducible]
  def event.regular (e : event) := e = e.exterior.exterior
  -- also called boundary
  -- @[reducible]
  -- def event.frontier (e : event) := frontier e
  
  -- EVENT LEMMAS
   -- And we prove some simple useful lemmas
   
   lemma event_union_exterior_open : ∀{e : event}, is_open e → is_open (e ∪ e.exterior) :=
   begin
      intros e h,
      apply is_open_union h,
      simp [event.exterior],
   end

   lemma event_nonempty_of_ne_empty : ∀{e : event}, e ≠ ∅ → e.nonempty :=
    begin
        intros e h,
        simp [set.nonempty],
        classical,
        by_contradiction h₂,
        replace h₂ := forall_not_of_not_exists h₂,
        simp at h₂,
        replace h₂ := eq_empty_iff_forall_not_mem.2 h₂,
        contradiction,
    end

   lemma event_union_exterior_nonempty : ∀{e : event}, (e ∪ e.exterior).nonempty :=
    begin
       intros e,
       apply event_nonempty_of_ne_empty,
       intro h,
       simp at h,
       obtain ⟨h₁, h₂⟩ := h,
       rw h₁ at h₂,
       simp [event.exterior] at h₂,
       contradiction,
    end

 -- ENTITIES 
 
  -- Particular (possible) `entities` in the ontology are nonempty open sets of worlds.
  -- An entity is said to `exist` precisely in those worlds which are its elements.
  structure entity :=
      -- the event of the entity existing
      (exist : event)
      (is_open : is_open exist)
      (ne : exist.nonempty)
  
  -- An entity `actually exists` if and only if it exists in the actual world.
  -- We say simply that it aexists, for short.
  @[reducible]
  def entity.aexists (e : entity) := e.exist.obtains
  
  -- Two entities are `contrary` if their intersection (as sets) is empty,
  -- they are otherwise `compatible`.
  @[reducible]
  def entity.contrary (e₁ e₂ : entity) := e₁.exist ∩ e₂.exist = ∅
  @[reducible]
  def entity.compatible (e₁ e₂ : entity) := (e₁.exist ∩ e₂.exist).nonempty
  
  -- Some very important entities have no contraries
  @[reducible]
  def entity.nocontrary (e : entity) := ¬ ∃ y, e.contrary y
  
  -- Entity x is said to existentially entail entitity y,
  -- or to existentially depend on y,
  -- if in every possible world in which x exists, y exists.
  -- For this relation we use the subset notation.
  
  instance entity.has_subset : has_subset entity := 
      ⟨λ x y : entity, x.exist ⊆ y.exist⟩

  -- The necessary being (entity) is the entity which exists in
  -- every possible world.
  def nbe : entity := ⟨univ,is_open_univ, by simp [empty_ne_univ]⟩
  
  -- Here are some more lemmas, these ones are more philosophical.
  
  -- Arbitrary nonempty unions of entities are entities.
  def entity_Sup (s : set entity) (h : s.nonempty) : entity :=
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
  def entity.inter (e₁ e₂ : entity) (h : e₁.compatible e₂) : entity :=
      ⟨  e₁.exist ∩ e₂.exist
      , is_open_inter e₁.is_open e₂.is_open
      , h
      ⟩
  
  -- We can also talk about an entity existing in a world
  -- as belonging to it, so we can use the notation e ∈ w.
  @[reducible]
  instance world.has_mem : has_mem entity world := ⟨λe w, w ∈ e.exist⟩
  @[reducible]
  def world.entities (w : world) := {e : entity | e ∈ w}
 
 -- SUBSTANCES
  -- DEFINITIONS

   -- Particular `substances` in the ontology are dense entities, every other entity is an `accident`.
   -- We also call a dense entity a perfect entity.
   @[reducible]
   def perfect (e : entity) := e.exist.dense
   @[reducible]
   def imperfect  (e : entity) := ¬ perfect e
   def substance := subtype {e : entity | perfect e}
   def accident := subtype {e : entity | imperfect e}
   
   -- By this definition, it is obvious that any entity 
   -- is either a substance or an accident, therefore we can
   -- cast it to one of them.
   
   noncomputable def antepredicament (e : entity) : substance ⊕ accident :=
   begin
      classical,
      by_cases perfect e,
          left,
          exact ⟨e, h⟩,
      right,
      exact ⟨e, h⟩,
   end

   -- The `necessary being` is the substance that exists in every possible world.
   def nb : substance := 
       ⟨nbe, by simp [nbe, set_of, perfect, event.dense]⟩
   
   instance substance.inhabited : inhabited substance := ⟨nb⟩
   
   -- A substance is `contingent` if it is not the necessary being.
   -- Since the nb is a substance, all accidents are informally contingent.
   def contingent (s : substance) := s ≠ nb
   
   -- The necessary being exists in the actual world.
   example : nb.val.aexists := by unfold nb; simp
   
   @[reducible]
   def world.substances (w : world) := {s : substance | s.val ∈ w}
   @[reducible]
   def world.accidents (w : world) := {a : accident | a.val ∈ w}
  
  -- LEMMAS

   -- The fundamental fact that justifies the definition of substances
   -- is that they admit no contrary entities, and this is a property
   -- explicitly mentioned in Aristotle's Categories, which suffices for
   -- their definition.

   lemma substance_nocontrary : ∀ s : substance, s.val.nocontrary :=
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

   lemma perfect_iff_nocontrary : ∀ e : entity, e.nocontrary ↔ perfect e :=
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
   lemma substance_of_substance_entails : ∀{s : substance}{e : entity},
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
   def substance_Sup (s : set substance) (h : s.nonempty) : substance :=
    begin
      fsplit,
          apply entity_Sup (subtype.val '' s),
          simp,
          exact h,
      simp [set_of, perfect, event.dense, entity_Sup],
      let i := h.some,
      have c : i.val.exist ⊆ (⋃ (i : substance) (H : i ∈  s), i.val.exist),
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
   def substance.inter (s₁ s₂ : substance) : substance :=
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
   instance substance.has_inter : has_inter substance := ⟨substance.inter⟩
   
   -- ACCIDENTS

    -- Nonempty finite intersections of accidents are accidents
    def accident.inter (a₁ a₂ : accident) (h : a₁.val.compatible a₂.val) : accident :=
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
      let β : substance := ⟨α, h₂⟩,
      have c₂ := @substance_of_substance_entails _ _ _ _ β a₁.val c₁,
      exact absurd c₂ a₁.property,
     end
  
  -- SUBSISTENCE AND INHERENCE

   -- An entity is said to `subsist` in another entity 
   -- if and only if the second can be written as the union of the first
   -- and its interior, or alternatively, as the complement of its boundary.
   
   def subsists (x y : entity) :=
      x.exist ∪ x.exist.exterior = y.exist
  
   @[reducible]
   def entity.subsistents (x : entity) := {y : entity | subsists y x}
   
   -- Inherence is the same relation defined between accidents and substances
   def inheres (a : accident) (s : substance) :=
      subsists a.val s.val
   
   lemma subset_of_subsist : ∀ x y, subsists x y → x.exist ⊆ y.exist :=
   begin
      intros x y h w hw,
      simp [subsists] at h,
      rw <-h,
      simp [hw],
   end
   
   lemma sub_of_inheres : ∀ a s, inheres a s → a.val.exist ⊆ s.val.exist :=
    by simp [inheres]; intros a s; exact subset_of_subsist a.val s.val
   
   @[reducible]
   instance substance.has_mem : has_mem accident substance := ⟨inheres⟩ 
   @[reducible]
   def substance.accidents (s : substance) := {a : accident | a ∈ s}
   
   -- Only substances can support accidents
   lemma sub_support :  ∀ {x}, (∃y, subsists y x) → perfect x :=
   begin
      intros x h,
      obtain ⟨y, h⟩ := h,
      simp [perfect, event.dense],
      simp [subsists] at h,
      rw ←h,
      simp [closure_union, event.exterior],
      ext, constructor; intro h₂,
          trivial,
      classical,
      by_cases x_1 ∈ closure (y.exist),
          simp [h],
      right,
      intro h₃,
      have c : x_1 ∈ closure (y.exist) := interior_subset h₃,
      contradiction,
   end
   
   -- An entity is a substance if and only if it subsists in itself.
   lemma self_subsist :  ∀ {x}, perfect x ↔ (subsists x x) :=
   begin
      intro x,
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
      existsi x,
      exact h,
   end
   
   -- Every accident inheres in a single substance, 
   -- therefore we can construct the substance from the accident.
   def substance_of (a : accident) : substance := 
      let e : entity := ⟨a.val.exist ∪ a.val.exist.exterior,
                        event_union_exterior_open a.val.is_open,
                        event_union_exterior_nonempty⟩ 
      in ⟨e, sub_support ⟨a.val, rfl⟩⟩
  
   @[simp]
   lemma inheres_sub_of : ∀{a}, a ∈ (substance_of a) :=
      by intro a; simp [inheres, substance_of, subsists]
  
   lemma unique_inheres : ∀ (a : accident) (s₁ s₂ : substance), a ∈ s₁ → a ∈ s₂ → s₁ = s₂ :=
   begin
      intros a s₁ s₂ h₁ h₂,
      obtain ⟨⟨s₁, op₁, ne₁⟩, pe₁⟩ := s₁,
      obtain ⟨⟨s₂, op₂, ne₂⟩, pe₂⟩ := s₂,
      simp [inheres, subsists] at *,
      rwa h₁ at h₂,
   end
   
   lemma unique_sub_of : ∀ a s₁ s₂, s₁ = substance_of a → s₂ = substance_of a → s₁ = s₂ :=
   begin
      intros a s₁ s₂ h₁ h₂,
      apply unique_inheres a;
      simp [substance_of, inheres, subsists, h₁, h₂],
   end
  
  -- SIMPLICITY

   -- An entity is called `simple` if it has no accidents.
   @[reducible]
   def simple (e : entity) := e.subsistents = ∅
   @[reducible]
   def composite (e : entity) := ¬ simple e
   
   -- All accidents are simple
   lemma acc_simp :  ∀ a : accident, simple a.val := 
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
 -- ACCIDENTS
  
  -- regular accidents are called intrinsic
  -- and irregular accidents are called extrinsic
  @[reducible]
  def intrinsic (a : accident) := a.val.exist.regular
  @[reducible]
  def extrinsic (a : accident) := ¬ a.val.exist.regular

  -- A connected intrin sic accident is called a quality
  structure quality :=
    (exist : event)
    (is_open : is_open exist)
    (ne : exist.nonempty)
    (imperfect : ¬ exist.dense)
    (intrinsic : exist.regular)
    (connected : is_preconnected exist)
 
  def quality.entity (q : quality) : entity := ⟨q.exist, q.is_open, q.ne⟩
  def quality.acc (q : quality) : accident := ⟨q.entity, q.imperfect⟩

  -- a disconnected intrinsic accident is a quantity
--   structure quantity :=
--     (acc : accident)
--     (intrinsic : intrinsic acc)
--     (is_disconnected : ¬ is_preconnected acc.val.exist)

  lemma exterior_of_accident_is_accident : ∀ {a : accident}, 
                                           is_open a.val.exist.exterior ∧
                                           a.val.exist.exterior.nonempty ∧
                                           ¬ a.val.exist.exterior.dense
                                           :=
    begin
        intros a,
        -- repeat{fsplit},
        split, admit,
        split, admit,
        admit,
    end
  
  def accident.exterior (a : accident) : accident := 
    ⟨⟨a.val.exist.exterior, exterior_of_accident_is_accident.1, exterior_of_accident_is_accident.2.1⟩,exterior_of_accident_is_accident.2.2⟩  

  lemma aux : ∀ (s : substance) (q : quality) 
              (S : set (subtype s.val.exist)),
              is_open S →
              is_connected S → 
              q.exist ⊆ subtype.val '' S →
              q.acc ∈ s →
              subtype.val '' S = q.exist :=
    begin
        intros s q S is_openS is_connectedS h₁ h₂,
        simp [set.image, subtype.val],
        ext, constructor; intros h; simp at *,
            obtain ⟨h, elem⟩ := h,
            have c : x ∈ q.exist ∪ q.exist.exterior,
                simp [inheres, subsists] at h₂,
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

 end particulars
 
section states
 -- Substances have `states`, altough the states of metaphysical
 -- substances are trivial.
 
 parameter (s : substance)
 
 -- The state of an entity at some 
 -- possible world viewed as a set of its accidents:
  def substance.state_set (w : world) : set accident :=
  s.accidents ∩ world.accidents w

 -- The state equivalence of possible worlds generated by a substance
 def substance.equiv (w₁ w₂ : world) :=
    s.state_set w₁ = s.state_set w₂

 lemma substance.equiv_sound : equivalence substance.equiv :=
  begin
    repeat{fsplit},
        simp [reflexive, substance.equiv],
        simp [symmetric, substance.equiv],
            intros x y h,
            rw h,
        simp [transitive, substance.equiv],
            intros x y z h₁ h₂,
            rwa ←h₁ at h₂,
  end

 def substance.state_setoid : setoid world :=
 ⟨s.equiv, s.equiv_sound⟩

 
 -- The type of states of a substance
 @[reducible]
 def substance.state := quotient s.state_setoid
 
 -- The quotient map from worlds to states,
 -- which ontologically grounds set of states as entities.
 @[reducible]
 def φ := @quotient.mk world s.state_setoid

 def substance.state_at (w : world) := φ w
 
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
 def substance.event := set substance.state
 
 structure substance.perfection :=
    -- the event of the perfection existing in the substance
    (exist : s.event)
    (is_open : is_open exist)
    (ne : exist.nonempty)
    (nuniv : exist ≠ univ)

 -- We added nuniv because the necessary s.event should not really
 -- be considered an internal perfection of the substance, since it
 -- is grounded in the nb and is always necessary.
 
 -- Accidents of a substance are perfections of the same substance.
 -- The most important step in this proof is to show that they are open.
 lemma state_open_of_accident : ∀ (a: accident), a ∈ s → is_open (φ '' a.val.exist) :=
 begin
    intros a H,
    apply is_open_coinduced.2,
    simp [preimage],
    let α := {x : world | ∃ (x_1 : world), x_1 ∈ (a.val).exist ∧ substance.equiv s x_1 x},
    suffices c : is_open α,
        exact c,
    suffices c : α  = a.val.exist,
        rw c,
        exact a.val.is_open,
    ext, constructor; intro h; simp at *,
        obtain ⟨y, h₁, h₂⟩ := h,
        simp [substance.equiv, substance.state_set] at h₂,
        simp [ontology.world.accidents, substance.accidents] at h₂,
        have c : {a : accident | inheres a s} ∩ {a : accident | y ∈ (a.val).exist} ⊆
                 {a : accident | inheres a s} ∩ {a : accident | x ∈ (a.val).exist},
        rw h₂,
        exact and.right (@c a ⟨H, h₁⟩),
    existsi x,
    constructor,
        assumption,
    obtain ⟨res, _, _⟩ := substance.equiv_sound s,
    exact res x,
 end
 
 -- It should then be easier to prove that it is not empty
 lemma state_ne_of_accident : ∀ (a: accident), a ∈ s → (φ '' a.val.exist).nonempty :=
 begin
    intros a H,
    simp [preimage],
    exact a.val.ne,
 end
 
 -- But it is a little bit harder to prove it is not univ
 lemma state_nuniv_of_accident : ∀ (a: accident), a ∈ s → (φ '' a.val.exist) ≠ univ :=
 begin
    intros a H,
    simp [preimage, image, quotient.mk],
    intro h,
    -- This is a trick
    -- let ψ := (@quotient.mk world ontology.substance.state_setoid),
    replace h : univ ⊆ {b : quotient ontology.substance.state_setoid | ∃ (a_1 : world), a_1 ∈ (a.val).exist ∧ φ s a_1 = b},
        rw ←h,
        -- refl,
    have c : s.val.exist = a.val.exist,
    ext, constructor; intro h₁; simp at *,
        have c := @h (φ s x) _,
        simp at c,
        obtain ⟨y, c₁, c₂⟩ := c,
        replace c₂ : substance.equiv s y x := c₂,
        simp [substance.equiv, substance.state_set] at c₂,
        simp [ontology.world.accidents, substance.accidents] at c₂,
        have c : {a : accident | inheres a s} ∩ {a : accident | y ∈ (a.val).exist} ⊆
                 {a : accident | inheres a s} ∩ {a : accident | x ∈ (a.val).exist},
        rw c₂,
        exact and.right (@c a ⟨H, c₁⟩),
            trivial,
        revert x,
        apply sub_of_inheres,
        exact H,
    have c₁ : s.val.exist.dense := s.property,
    have c₂ : ¬ a.val.exist.dense := a.property,
    rw c at c₁,
    contradiction,
 end
 
 -- Finally we can construct the perfection.
 def perfection_of (a ∈ s) : s.perfection :=
    -- assume a,
    -- assume H : a ∈ s,
    ⟨ φ '' a.val.exist
    , state_open_of_accident a H
    , state_ne_of_accident a H
    , state_nuniv_of_accident a H
    ⟩

 -- perfections which come from accidents
 @[reducible]
 def substance.aperfections := {p : s.perfection | ∃ a ∈ s, (perfection_of a H) = p}
 
 -- events which come from accidents
 @[reducible]
 def substance.aevents := {p : s.event | ∃ a ∈ s, (perfection_of a H).exist = p}
 
 instance state_has_mem : has_mem s.perfection s.state :=
 ⟨λ p s, s ∈ p.exist⟩
 @[reducible]
 def perfections (x : s.state) := {p : s.perfection | p ∈ x}

 -- We can also build a neighborhood for any state
 -- which is an aperfection in case the substance has
 -- accidents in that state and the whole space otherwise.

 structure nhd {s : substance} (x : s.state) :=
    (U : s.event)
    (is_open : is_open U)
    (elem : x ∈ U)

 noncomputable def state.nhd_default {s : substance} (x : s.state) : nhd x :=
    begin
        classical,
        set elab_help := s.state_setoid,
        -- lets build a world which maps to x
        -- and has some accident, the associated perfection of which
        -- will be our neighborhood. If no such world exists, we
        -- will just use univ.
        by_cases w : ∃w, ⟦w⟧ = x ∧ (∃a : accident, a ∈ s ∧ a.val ∈ w),
        swap,
            exact ⟨univ, is_open_univ, by simp⟩,
        replace w := nonempty_subtype.2 w,
        replace w := classical.choice w,
        obtain ⟨w, hw, a⟩ := w,
        replace a := nonempty_subtype.2 a,
        replace a := classical.choice a,
        obtain ⟨a, ha₁, ha₂⟩ := a,
        -- a is now our wanted accident.
        let p := perfection_of s a ha₁,
        -- it is now easier to build the neighborhood.
        fconstructor,
            exact p.exist,
            exact p.is_open,
        rw ←hw,
        simp [p,perfection_of],
        existsi w,
        exact ⟨ha₂, rfl⟩,
    end

 -- Each contingent substance has a bottom state. For a contingent substance
 -- this is the "state" in which the substance does not exist.
 
 --  lemma aux : contingent s → ∀ w, 
 
 --  def aux (h : contingent s) : nonempty (subtype s.val.exist.compl) := sorry
  
 --  @[reducible]
 --  noncomputable def state_bot (h : contingent s) : s.state :=
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
 --     set s : substance := ⟨⟨exist, is_open, nes⟩, perfect⟩,
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
 --  lemma bot_no_accidents (h : contingent s) : (s.state_set (@quotient.out _ s.state_setoid (state_bot h))) = ∅ :=
 --     begin
 --         set elab_help := s.state_setoid,
 --         simp [substance.state_set],
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
 --     set elab_help := s.state_setoid,
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
 --  instance state_order_bot : order_bot s.state :=
 --   begin
 --     classical,
 --     fconstructor,
 --         by_cases contingent s,
 --             obtain ⟨⟨exist, is_open, nes⟩, perfect⟩ := s,
 --             simp [contingent, nb, nbe] at h,
 --             set s : substance := ⟨⟨exist, is_open, nes⟩, perfect⟩,
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
 --     exact ∀ p : s.perfection, p ∈ x₁ → p ∈ x₂,
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
 --  lemma accidents_nhds : ∀ (w : s.state) (U : set s.state), w ∈ U → is_open U → ∃ V ∈ s.aevents, w ∈ V ∧ V ⊆ U :=
 --  begin
 --      intros w U H op,
 --  end
 
 --  #check is_topological_basis_of_open_of_nhds
 
 -- Then we want to show that unions of accidents also map
 -- to perfections, and that all perfections are generated this way.


 end states



section universals

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
 class inductive abstraction : Π (α : Type u) [topological_space α], Type (u+1)
  | particular (s : substance) : abstraction s.state
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

 instance particular (s : substance) : abstraction s.state := abstraction.particular s 

 -- CONCEPTS

  -- A concept for a Type is a topology
  -- for that Type that was abstracted away
  -- from the particular substances.
  -- It is a "concrete universal", an
  -- universal not defined up to isomorphism.
  inductive concept : Type (u+1)
  | mk   (state : Type u)
         [t : topological_space state]
         [abs : abstraction state]
         : concept

  def substance.concept (s : substance) : concept := ⟨s.state⟩
 
  def concept.state (c : concept) : Type u :=
    by obtain ⟨state, _, _⟩ := c; exact state

  instance concept.t (c : concept) : topological_space c.state := 
    by obtain ⟨_, t, _⟩ := c; exact t
 
  instance concept.abs (c : concept) : abstraction c.state := 
    by obtain ⟨_, _, abs⟩ := c; exact abs

  -- concepts are inhabited by the concept of a
  -- necessary being.
  instance concept_inhabited : inhabited concept := ⟨nb.concept⟩
 
  variable c : concept
 
  @[reducible]
  def concept.event := set c.state
  
  -- Concepts can have world indexed states just as substances
  -- but the concept doesnt just make sense for just any concept,
  -- so occasionally we can associate a nonempty set of states to
  -- a concept and occasionally it will be empty 
  -- (namely, if the concept is defined as a subconcept of another concept).
  def concept.state_at (w : world) : c.event :=
    begin
        cases c,
        induction c_abs,
            exact {c_abs.state_at w},
        all_goals {
            dunfold concept.event concept.state,
            simp,
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
 def state_preserving {c₁ c₂ : concept} (f : c₁.state → c₂.state) :=
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
  def concept.grounded (c : concept) : set substance :=
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
  def integral_whole (s : set substance) : concept :=
  let get := λx : subtype s, x.val.state,
      type := Π i : subtype s, (get i)
  in begin
    set abs := abstraction.pi get (by apply_instance),
    exact @concept.mk type _ abs,
  end

  def abstract_whole (s : set substance) : concept :=
  let get := λx : subtype s, x.val.state,
      type := Σ i : subtype s, (get i)
  in begin
    set abs := abstraction.sigma get (by apply_instance),
    exact @concept.mk type _ abs,
  end 

 -- UNIVERSALS

  -- Since universals will 
  -- be equivalence classes of concepts, 
  -- we need to define a setoid of concepts.

  -- Two concepts are equivalent if they are homeomorphic
  @[reducible]
  def concept_equiv (c₁ c₂ : concept) :=
    nonempty (c₁.state ≃ₜ c₂.state)

  instance concept_setoid : setoid concept :=
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
  def universal := quotient concept_setoid
 
  -- In order to the define the concept of `essence` and that of
  -- `definition` we require the definition of an invariant property.
  @[reducible]
  def property := concept → Prop
  def property.invariant (p : property) :=
    ∀ c₁ c₂ : concept, 
    c₁ ≈ c₂ → (p c₁ ↔ p c₂)

  -- The essence of an universal is a property which defines
  -- its concepts up to homeomorphism.
  def universal.is_essence (u : universal) (p : property) :=
    p.invariant ∧
    ∃ c₁, ⟦c₁⟧ = u ∧ p c₁ ∧
    (∀ c₂, p c₂ → c₁ ≈ c₂)

  @[reducible]
  def universal.essence (u : universal) := subtype u.is_essence
 
  -- every universal has an essence
  theorem essentialism : ∀ u : universal, nonempty u.essence :=
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
                suffices h : ∀ (c₁ c₂ : concept), c₁ ≈ c₂ → (c ≈ c₁ → c ≈ c₂),
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
  def concept.instantiable : property := λc, ∃ s : substance, s.concept ≈ c
 
  -- Instantiability is of course an invariant
  lemma concept_instantiable_invariant : concept.instantiable.invariant :=
    begin
        dunfold concept.instantiable property.invariant,
        intros c₁ c₂ h,
        suffices c : (∃ (s : substance), substance.concept s ≈ c₁) → ∃ (s : substance), substance.concept s ≈ c₂,
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
  def universal.instantiable (u : universal) := u.out.instantiable
 
  -- TODO: argue that Aquinas defended the u.out point of view in
  -- De ente et essentia.
 
  -- The nb as an universal.
  @[reducible]
  def nbu : universal := ⟦nb.concept⟧
  instance universal_inhabited : inhabited universal := ⟨nbu⟩
 
  -- A notion is a quality defined abstractly in the representation
  def universal.notion (u : universal) := u.out.quality 


 end universals
section categories
 
 -- A definition of the 10 Aristotelian Categories,
 -- and of the subcategories Aristotle mentions in his work.
 -- The Categories of Substance and Quality were already defined.

 variable c : concept

 -- A quantity for a concept is a continuous
 -- map from states of the concept to the reals.
 def concept.quantity := subtype {f : c.state → ℝ | continuous f }

 --  For some reason which is mind boggling, we couldn't
 --  find the definition of a probability measure in mathlib.
 instance concept.borel : measurable_space c.state := borel c.state
 def concept.probability_measure := {μ : measure_theory.measure c.state | μ.measure_of univ = 1} 

 -- A disposition is a partly state-indexed probability measure for a concept
 -- such that the preimage of every probability measure is either open or closed.
 def concept.disposition := 
    subtype {f : c.state →. c.probability_measure | ∀ p : c.probability_measure, is_open (f⁻¹' {roption.some p}) ∨ is_closed (f⁻¹' {roption.some p})}

 -- A habit is a "permanent" disposition. We take this to mean that
 -- it is constant in a dense open set.
 def concept.habit := 
    subtype {d : c.disposition | ∃ p : c.probability_measure,  closure (d.val⁻¹' {roption.some p}) = univ}

 -- a law of nature is a constant disposition, i.e. the same for every
 -- state. It is provably a habit as well. 
 -- The usual talks of "laws of nature" are laws of nature in the "cosmos"
 -- (to be defined later), assuming that these laws are necessary. But if
 -- they are contingent they are assumed to be habits.

 def concept.law := 
    subtype {d : c.disposition | ∃ p : c.probability_measure, ∀ x : c.state, p ∈ d.val x}


 end categories
section matter

 -- We call any composite substance `physical`,
 -- or a `body`.
 
 @[reducible]
 def physical (s : substance) := composite s.val
 def cosmos_set := {s : substance | physical s}
 def body := subtype cosmos_set
 
 -- The cosmos is the integral whole of all
 -- composite (physical) substances.
 def cosmos := integral_whole cosmos_set

 -- Prime matter is the abstract whole of all
 -- composite (physical) substances.
 def prime_matter := abstract_whole cosmos_set
 
 -- There are specifically two dual notions of `matter` that are obtained 
 -- by considering virtual substances (concepts) 
 -- as the totalities of both kinds of matter:
 
 -- (1) From the point of view of the whole, 
 -- matter can be thought of as that which 
 -- actively composes a thing, its substratum.
 -- This sense we will only cover in the next
 -- section, which is mereology.
 
 -- (2) From the point of view of matter itself,
 -- matter can be thought of as that which is in potency
 -- to a multiplicty of forms, in the sense of prime matter.
 -- Mathematically these two notions are dual, 
 -- with the duality of Π and Σ types, respectively.

 -- Notice, in the first notion matter is actual, 
 -- and in the second potential.
 
 -- Transcendent matter is the abstract whole of all
 -- substances.
 -- This is the virtual substance that is "in potency"
 -- for becoming any other substance.
 def transcendent_matter : concept := abstract_whole univ

 -- The state space of a virtual, likely possible, substance
 -- corresponding to a concrete and immanent notion of matter.
 -- This virtual is the mereological sum of the set of all substances.
 -- It is the whole of reality.
 def reality : concept := integral_whole univ

 -- Of course nothing in reality is an instance of
 -- prime or transcendent matter.

 end matter
section mereology

 -- A substance s₁ is an integral part of another
 -- substance s₂ if there is a 
 -- (necessarilly nonempty) set S of substances 
 -- such that the integral whole of {s₁} ∪ S is
 -- homeomorphic to the state space of s₂ by
 -- means of a state-preserving homeomorphism
 def substance.part_of (s₁ s₂ : substance) :=
    -- s₁ ≠ s₂ ∧
    ∃ S : set substance, 
    S.nonempty ∧
    s₁ ∉ S ∧
    -- (∀ x ∈ S, x ≠ s₂) ∧
    ∃ hom :
        s₂.concept.state ≃ₜ
        (integral_whole $ S ∪ {s₁}).state,
    state_preserving hom.to_fun

 -- This is to say that if we know the state of the
 -- substance s₂ in a possible world w, then we
 -- already know the state of each of its parts,
 -- since there is a functional dependence between them.


 --  lemma
 
 --  @[trans]
 --  lemma part_of_trans : ∀ s₁ s₂ s₃ : substance, 
 --                        s₁.part_of s₂ →
 --                        s₂.part_of s₃ →
 --                        s₁.part_of s₃ :=
 --     begin
 --         intros s₁ s₂ s₃ h₁ h₂,
 --         -- simp [substance.part_of] at *,
 --         obtain ⟨S₁, ne₁, notin₁, hom₁, h₁⟩ := h₁,
 --         obtain ⟨S₂, ne₂, notin₂, hom₂, h₂⟩ := h₂,
 --         use S₁ ∪ S₂ ∪ {s₂},
 --     end

 end mereology
section causality
 end causality
section metaphysics

 -- We call a substance `metaphysical`, or a `separate substance`, if it is simple.
 -- It is otherwise `physical`, or a `body`, as already mentioned.
 @[reducible]
 def metaphysical (s : substance) := simple s.val
 def separate := subtype {s : substance | metaphysical s}
 
 -- A substance is purely actual if it has no passive potency
 -- to be different from what it is, i.e. if it has a single state.
 def purely_actual (s : substance) := nonempty (s.state ≃ unit)
 
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
 
 -- Platonism in the broad sense (greek theism) is the doctrine 
 -- that the necessary being is metaphysical
 def platonism := metaphysical nb
 
 -- The admission of any metaphysical substance entails platonism
 lemma platonism_of_nonempty_separate : nonempty separate → platonism :=
 sorry
 end metaphysics
section theology
 
 -- (Classical) Theism is an extension of Platonism which 
 -- furthermore claims that there is a possible world 
 -- in which the necessary being exists alone.
 def theism := platonism ∧ ∃ (w : world), world.entities w = {nb.val}
 
 end theology
section ethics
 end ethics
end ontology
end ontology
