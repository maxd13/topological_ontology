import ontology
universe u
open set topological_space classical
local attribute [instance] prop_decidable


/-! # Substances and accidents

In this module we define the notions of `substance`, `accident`,
`subsistence`, `inherence`, `cosubstantiality`, `simplicity` and 
the distinction between `intrinsic` and `extrinsic` accidents.

We also prove several lemmas associated with these concepts.

-/

namespace ontology

variable {ω : ontology}

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


 -- main extensionality lemma for substances.
 @[ext]
 lemma substance.ext {s₁ s₂ : ω.substance} (h : s₁.val = s₂.val) : s₁ = s₂ := sorry

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
 @[simp] lemma self_subsist {e : ω.entity} : e.perfect ↔ (e.subsists e) :=
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
 lemma sub_self_subsist : s.val.subsists s.val := self_subsist.mp s.property

  
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
 @[reducible]
 def substance.simple (s : ω.substance) := simple s.val
 @[reducible]
 def substance.composite (s : ω.substance) := ¬ simple s.val

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
      let β : ω.substance := ⟨α, self_subsist.2 h₂⟩,
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


end ontology