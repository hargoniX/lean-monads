import Monads.Functor

namespace Monads
  /- Applicative functors allow us to apply functions that are already
     wrapped withing the functor to other values wrapped withing the functor.
     This allows chaining of methods like so: f <$> g <*> h <*> x. -/
  class Applicative (f : Type u → Type v) extends Functor f where
    /- Lift a normal value into an applicative context. -/
    pure : α → f α
    /- Apply a function inside an applicative to a value inside an applicative. -/
    apply : ∀ {α β : Type u}, f (α → β) → f α → f β
    /- Lift a funcion of arity 2 (2 parameters) to the applicative context. -/
    liftA2 : (α → β → γ) → f α → f β → f γ := λ g x y => apply (g <$> x) y
    /- Drop the action on the left and only return the right one. If
       left contains e.g. a sideffect it will still be executed. -/
    seq_right : f α → f β → f β := λ a1 a2 => apply (id <$ a1) a2
    /- Drop the action on the right and only return the left one. If
       right contains e.g. a sideffect it will still be executed. -/
    seq_left : f α → f β → f α := liftA2 (Function.const β)

  export Applicative (pure liftA2)

  infixl:60 " <*> " => Monads.Applicative.apply
  -- The arrow points at the value that is kept
  infixl:60 " *> " => Monads.Applicative.seq_right
  infixl:60 " <* " => Monads.Applicative.seq_left


  /- Lawful applicatives essentially capture the same concept of modifying
     only the contents and not the context they are captured in as a lawful
     regular functor. -/
  class LawfulApplicative (f : Type u → Type v) [app: Applicative f] extends LawfulFunctor f : Prop where
    /- If the function maps values to themselves the values in the applicative
       shall remain unchanged. -/
    apply_id : ∀ x : f α, pure id <*> x = x
    /- Applying a pure function to a pure value with <*> shall be the
       same as first applying them outside of the applicative and wrapping
       the result into it. -/
    apply_homomorphism: ∀ (x : α) (g : α → β), pure g <*> app.pure x = pure (g x)
    /- Applying an effectful function to a pure value should yield the same result,
       regardless of order. -/
    apply_interchange: ∀ {α β : Type u} (x : α) (g : f (α → β)), g <*> pure x = pure (· $ x) <*> g
    /- A modified associativity property for <*>. -/
    apply_comp : ∀ {α β γ: Type u} (x : f (β → γ)) (y : f (α → β)) (z : f α), pure (@Function.comp α β γ) <*> x <*> y <*> z = x <*> (y <*> z)
    /- If there is a custom liftA2 definition it has to behave like the default one -/
    lifta2_behaved : ∀ (g : α → β → γ) (x : f α) (y : f β), liftA2 g x y = g <$> x <*> y 
    /- If there is a custom *> definition it has to behave like the default one -/
    seq_right_behaved : ∀ (a1 : f α) (a2 : f β), a1 *> a2 = (id <$ a1) <*> a2
    /- If there is a custom <* definition it has to behave like the default one -/
    seq_left_behaved : ∀ (a1 : f α) (a2 : f β), a1 <* a2 = liftA2 (Function.const β) a1 a2
    /- This law is rather intuitive and provable with the free theorem in Haskell.
       However I'm unsure whether it applies in lean and no formalization exists,
       hence it will be an axiom. (Mathlib does this too). Furthermore it is shown
       below that the right hand side is a lawful functor. -/
    fmap_eq_pure_apply : ∀ (g : α → β) (x : f α), g <$> x = app.pure g <*> x


  namespace LawfulApplicative
    variable {f : Type u → Type v} [Applicative f] [LawfulApplicative f]
    -- These 4 laws allow us to prove equality of any term involving only <*> or pure (if they are equal)
    example {α β : Type u} {g : f (α → β)} {x : f α} : g <*> (pure id <*> x) = g <*> x := by rw [apply_id]
    example {α β : Type u} {g : f (α → β)} {x : f α} : pure id <*> (g <*> x) = g <*> x := by rw [apply_id]
    example {α β γ δ ε: Type u} {h : f (δ → ε)}{g : α → β → γ → δ} {x : α} { y : β} { z : γ} : h <*> (pure g <*> pure x <*> pure y <*> pure z) = h <*> pure (g x y z) := by
      simp only [apply_homomorphism]

    -- Constructing a lawful functor from a lawful applicative
    def apply_fmap : (α → β) → f α → f β := λ g a => pure g <*> a

    -- First law
    example : ∀ {α : Type u} (x : f α), apply_fmap id x = x := by
      intro α x
      simp only [apply_fmap]
      rw [apply_id]

    -- Second law
    example : ∀ {α β γ : Type u} (g : α → β) (h : β → γ) (x : f α), apply_fmap (h ∘ g) x = apply_fmap h (apply_fmap g x) := by
      intro α β γ g h x
      simp only [apply_fmap]
      rw [←apply_comp]
      rw [apply_homomorphism]
      rw [apply_homomorphism]
  end LawfulApplicative
end Monads
