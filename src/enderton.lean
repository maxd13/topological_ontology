import data.set.countable tactic.find tactic.tidy tactic.ring
universe u

-- We introduce a much simplified version of
-- untyped first order (minimal) predicate logic.

-- make all propositions decidable. 
-- Allows us to freely use ifs like in Haskell
-- but then we must add noncomputable to all functions
-- local attribute [instance] classical.prop_decidable


namespace logic

open logic list tactic set

section formulas
parameters {functional_symbol : Type u} [decidable_eq functional_symbol]
parameter {relational_symbol : Type u}
parameter {arity : functional_symbol -> ℕ}
parameter {rarity : relational_symbol -> ℕ}

-- arity types
def is_constant (f : functional_symbol) := arity f = 0
def nary (n : ℕ) := subtype {f : functional_symbol | arity f = n}
def nrary (n : ℕ) := subtype {r : relational_symbol | rarity r = n}
@[reducible]
def const := nary 0

-- terms in the language
inductive term
| var : ℕ → term
| app  {n : ℕ} (f : nary n) (v : fin n → term) :  term

-- constant terms.
def const.term : const → term
| c := term.app c fin_zero_elim

def term.rw : term → ℕ → term → term
| (term.var a) x t := if x = a then t else term.var a
| (term.app f v) x t := 
    let v₂ := λ m, term.rw (v m) x t in
    term.app f v₂

def term.vars : term → list ℕ
| (term.var a) := [a]
| (term.app  f v) :=
    let v₂ := λ m, term.vars (v m) in
    foldr (++) [] (of_fn v₂)

@[reducible]
def term.denotes (t : term) := t.vars = []
@[reducible]
def term.conotes (t : term) := ¬ t.denotes

theorem aux_rw : ∀ (t₁ t₂ : term) (x : ℕ), x ∉ t₁.vars → t₁.rw x t₂ = t₁ :=
    sorry

-- a term in the proper sense of the term (pun intended).
def pterm := subtype {t : term | t.denotes}
def expression := subtype {t : term | t.conotes}

def list.vars : list term → list ℕ
| [] := ∅
| (hd :: tl) := hd.vars ++ tl.vars

-- formulas
inductive uformula
| relational {n : ℕ} (r : nrary n) (v : fin n → term) : uformula
-- | equation (t₁ t₂ : term) : uformula
| false : uformula
| for_all :  ℕ → uformula → uformula
| if_then : uformula → uformula → uformula

def uformula.not (φ) := uformula.if_then φ uformula.false

class has_exp (α : Type u) := (exp : α → α → α)
infixr ⇒ := has_exp.exp
instance uformula.has_exp : has_exp uformula := ⟨uformula.if_then⟩

local notation `∼` := uformula.not

def uformula.rw : uformula → ℕ → term → uformula
| (uformula.relational r v) x t :=
    let v₂ := λ m, (v m).rw x t in
    uformula.relational r v₂
-- | (uformula.equation t₁ t₂) x t :=
    -- let t₃ := t₁.rw x t,
    --     t₄ := t₂.rw x t
    -- in uformula.equation t₃ t₄
| (uformula.for_all y φ) x t :=
    let ψ := if y = x then φ else φ.rw x t in
    uformula.for_all y ψ
| (uformula.if_then φ ψ) x t := uformula.if_then (φ.rw x t) (ψ.rw x t)
| φ _ _ := φ


def list_sub_aux {α} [decidable_eq α] : list α → list α → list α
| [] _ := []
| (hd::tl) xs := 
begin
    cases list.decidable_mem hd xs,
        exact hd :: list_sub_aux tl xs,
    exact list_sub_aux tl xs,
end
                
instance list_sub {α} [decidable_eq α] : has_sub (list α) :=
⟨list_sub_aux⟩

-- free variables
def uformula.free : uformula → list ℕ
| (uformula.relational r v) := list.vars (of_fn v)
-- | (uformula.equation t₁ t₂) := t₁.vars ++ t₂.vars
| (uformula.for_all x φ) := φ.free - [x]
| (uformula.if_then φ ψ) := φ.free ++ ψ.free
| _ := []

def uformula.substitutable  : uformula → ℕ → term → Prop
| (uformula.relational r v) _ _ := true
| uformula.false _ _ := true
| (uformula.for_all y φ) x t := x ∉ (uformula.for_all y φ).free ∨
                                (y ∉ t.vars ∧ φ.substitutable x t) 
| (uformula.if_then φ ψ) y t := φ.substitutable y t ∧ ψ.substitutable y t

-- open and closed formulas.
def uformula.closed : uformula → Prop
| φ := φ.free = ∅

def uformula.open : uformula → Prop
| φ := ¬ φ.closed

def uformula.vars : uformula → list ℕ
| (uformula.for_all x φ) := x::φ.free
| (uformula.if_then φ ψ) := φ.vars ++ ψ.vars
| φ := φ.free

-- construct the generalization of a formula from a list of variables.
-- This is just a fold but, I like being explicit in my folds when possible.
def uformula.generalize : uformula → list ℕ → uformula
| φ [] := φ
| φ (x::xs) := uformula.for_all x $ φ.generalize xs

theorem uformula_rw : ∀ (φ : uformula)(t : term) (x : ℕ), x ∉ φ.free → φ.rw x t = φ :=
    sorry

inductive uaxiom : uformula → Prop
| p₁ (φ ψ : uformula) : uaxiom (φ ⇒ ψ ⇒ φ)
| p₂ (φ ψ δ : uformula) : uaxiom ((φ ⇒ ψ ⇒ δ) ⇒ ((φ ⇒ ψ) ⇒ φ ⇒ δ))
| p₃ (φ ψ : uformula) : uaxiom ((∼φ ⇒ ∼ψ) ⇒ ψ ⇒ φ)
| q₅ (x : ℕ) (φ : uformula) (t : term) (h : φ.substitutable x t) : uaxiom ((uformula.for_all x φ) ⇒ φ.rw x t)
| q₆ (x : ℕ) (φ ψ : uformula) : uaxiom ((uformula.for_all x φ ⇒ ψ) ⇒ (uformula.for_all x φ) ⇒ (uformula.for_all x ψ))
| q₇ (x : ℕ) (φ : uformula) (x ∉ φ.free) : uaxiom (φ ⇒ (uformula.for_all x φ))
| generalization (φ : uformula) (xs : list ℕ) (h : uaxiom φ) : uaxiom (φ.generalize xs)

def deduction (Γ : set uformula) : list uformula → Prop
| [] := true
| (φ::xs) := (φ ∈ Γ ∨ uaxiom φ ∨ ∃ ψ ∈ xs, (ψ ⇒ φ) ∈ xs) ∧
             deduction xs

@[reducible]
def uformula.theorem_of (φ : uformula) (Γ : set uformula) : Prop :=
    ∃ xs, deduction Γ (φ::xs)

local infixr `⊢`:55 := λ Γ (φ : uformula), φ.theorem_of Γ

variables (Γ : set uformula) (φ : uformula)

theorem self_entailment : Γ ⊢ (φ ⇒ φ) :=
begin
    let α₁ := φ ⇒ (φ ⇒ φ) ⇒ φ,
    let α₂ := (φ ⇒ (φ ⇒ φ) ⇒ φ) ⇒ ((φ ⇒ (φ ⇒ φ)) ⇒ φ ⇒ φ),
    let α₃ := φ ⇒ (φ ⇒ φ),
    let α₄ := (φ ⇒ (φ ⇒ φ)) ⇒ φ ⇒ φ,
    let α₅ := φ ⇒ φ,
    let xs := [α₅, α₄, α₃, α₂, α₁],
    use xs,
    unfold deduction,
    simp,
    repeat{fsplit},
        right,
        right,
        use α₃,
        simp,
    right,
    right,
    use α₃,
    simp,
        right,
        right,
        use α₁,
        simp,
    right,
    left,
    exact uaxiom.p₁ φ φ,
        right,
        left,
        exact uaxiom.p₂ φ (φ ⇒ φ) φ,
    right,
    exact uaxiom.p₁ φ (φ ⇒ φ),
end

section semantics

parameters {α : Type u} [nonempty α]

-- functional interpretation
def fint  {n : ℕ} := nary n → (fin n → α) → α
-- relational interpretation
def rint {n : ℕ} := nrary n → (fin n → α) → Prop
-- variable assignment
def vasgn := ℕ → α

structure model :=
    (I₁ : Π {n}, @fint n)
    (I₂ : Π {n}, @rint n)

def model.reference' (M : model) : term → vasgn → α
| (term.var x) asg := asg x
| (@term.app _ _ _   0 f _) _ := model.I₁ M f fin_zero_elim
| (@term.app _ _ _  (n+1) f v) asg := let v₂ := λ k, model.reference' (v k) asg
                                             in model.I₁ M f v₂

def vasgn.bind (ass : vasgn) (x : ℕ) (val : α) : vasgn :=
    λy, if y = x then val else ass y


lemma bind : ∀ (ass : vasgn) (x : ℕ), ass.bind x (ass x) = ass :=
    sorry

lemma bind₂ : ∀ (ass : vasgn) (x : ℕ) a b, (ass.bind x a).bind x b = ass.bind x b :=
    sorry

def model.satisfies' : model → uformula → vasgn → Prop
| M (uformula.relational r v) asg := 
          M.I₂ r $ λm,  M.reference' (v m) asg
| M uformula.false _ := false
| M (uformula.for_all x φ) asg :=
    ∀ (a : α),
    M.satisfies' φ (asg.bind x a)
| M (uformula.if_then φ ψ) asg :=
    let x := model.satisfies' M φ asg,
        y := model.satisfies' M ψ asg
    in x → y

@[reducible]
def model.satisfies : model → uformula → Prop
| M φ := ∀ (ass : vasgn), M.satisfies' φ ass

class has_vDash (M φ : Type u) :=
    (vDash : M → φ → Prop)

local infixr `⊨`:55 := has_vDash.vDash

instance model_formula : has_vDash model uformula := 
    ⟨model.satisfies⟩

lemma false_is_unsat : ¬∃ M : model, M ⊨ uformula.false :=
begin
    intro h,
    obtain ⟨M, h⟩ := h,
    revert h,
    dunfold has_vDash.vDash model.satisfies model.satisfies',
    intro h,
    apply nonempty.elim _inst_2,
    intro x,
    exact h (λ_, x),
end

lemma rw_bind : ∀ {M:model} {ass : vasgn} {φ} {x} {t} , 
                M.satisfies' φ 
                (ass.bind x (M.reference' t ass)) → 
                M.satisfies' (φ.rw x t) ass :=
    begin
        intros M ass φ x t h,
        induction φ,
        all_goals {
            tactic.unfreeze_local_instances,
            dunfold uformula.rw model.satisfies' at *,
            try{simp at * <|> contradiction},
        },
        convert h,
        ext,
        focus {
            induction φ_v x_1,
                dunfold term.rw model.reference',
                by_cases hyp : x = a;
                    simp [vasgn.bind, hyp],
                dunfold model.reference',
                cc,
            cases n;
            dunfold term.rw model.reference';
            simp,
            congr,
            ext,
            exact ih x_2,
        },
        set asg := ass.bind x (M.reference' t ass),
        have c := h (asg φ_a),
        simp [bind] at c,
        specialize φ_ih c,
        intro a,
        by_cases hyp : φ_a = x;
            simp [hyp],
            specialize h a,
            simp [asg, hyp, bind₂] at h,
            exact h,
        admit,
            -- revert φ_a_1,
            -- revert φ_a,
            -- intro x,
            -- generalize' : φ_a = x,
            -- intros φ h₁,
            intro hyp,
            repeat{apply_assumption <|> assumption},
        -- revert ass,
        -- simp,
            

    end

def model.for : model → set uformula → Prop
| M Γ := ∀ φ ∈ Γ, M ⊨ φ

-- semantic consequence
-- remember Γ and φ are already defined
def theory.follows : Prop :=
    ∀ (M : model), M.for Γ → M ⊨ φ

-- For some reason class resolution isnt working here
-- instance theory_formula : has_vDash (set uformula) uformula :=
--     ⟨theory.follows⟩

local infixr `⊨₁`:55 := theory.follows



theorem uaxiom_valid : uaxiom φ → Γ ⊨₁ φ :=
    begin
        intros h M for ass,
        induction h;
        try{dunfold model.satisfies', simp},
        -- case p₁
        intros h₁ _,
        exact h₁,
        -- case p₂
        intros h₁ h₂ h₃,
        exact h₁ h₃ (h₂ h₃),
        -- case p₃
        dunfold uformula.not model.satisfies',
        simp,
        intro h,
        contrapose,
        exact h,
        -- case p₄
        intro h,
        specialize h (M.reference' h_t ass),
        exact rw_bind h,
        -- case p₅

        -- induction h_φ;
        -- try{
        --     revert h_h, 
        --     dunfold uformula.substitutable 
        --             model.satisfies'
        --             uformula.rw,
        --     simp,
        -- },
        -- dunfold vasgn.bind,
        -- intro h,
        -- let ref := M.reference' h_t ass,
        -- specialize h ref,
        -- set x₁ := (λ (m : fin h_φ_n), M.reference' (h_φ_v m) (λ (y : ℕ), ite (y = h_x) ref (ass y))),
        -- set x₂ := (λ (m : fin h_φ_n), M.reference' ((h_φ_v m).rw  h_x h_t) ass),
        -- suffices c : x₁ = x₂,
        --     rwa c at h,
        -- ext,
        -- simp [x₁, x₂],
        -- induction h_φ_v x,
        --     dunfold term.rw model.reference',
        --     by_cases h₂ : a = h_x;
        --         simp [h₂],
        --     have c : ite (h_x = a) h_t (term.var a) = (term.var a),
        --         cc,
        --     rw c,
        --     dunfold model.reference',
        --     refl,
        -- cases n;
        -- dunfold term.rw model.reference';
        -- simp,
        -- set x₃ := (λ (k : fin (n + 1)), M.reference' (v k) (λ (y : ℕ), ite (y = h_x) ref (ass y))),
        -- set x₄ := (λ (k : fin (n + 1)), M.reference' ((v k).rw h_x h_t) ass),
        -- suffices c : x₃ = x₄, cc,
        -- ext,
        -- simp [x₃, x₄],
        -- exact ih x_1,
        -- -- another goal
        -- dunfold uformula.rw model.satisfies',
        -- revert h_h,
        -- dunfold uformula.substitutable uformula.free,
        -- intros h₁ h₂ x,
        -- specialize h₂ (ass h_x),
        -- rw (bind ass h_x) at h₂,
        -- by_cases h_φ_a = h_x;
        --     simp [h],
        --     rw ←h,
        --     exact h₂ x,
        -- cases h₁,
        --     admit,
        -- obtain ⟨h₁, h₂⟩ := h₁,
        -- --     apply h_φ_ih h₂,
        
    end


-- So pretty.
-- theorem soundness : (Γ ⊢ φ) → (Γ ⊨₁ φ) :=
-- begin
--     admit,
-- end



end semantics

section consistency
end consistency

end formulas
end logic