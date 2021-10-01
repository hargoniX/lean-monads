import Monads.Applicative

namespace Monads
  /- The monad is a close relativ to the applicative, however unlike
     an applicative functor it is in fact able to change the structure
     of the context the value is wrapped in since it allows users to
     pass a function that produces a new structure: (α → m β) -/
  class Monad (m : Type u → Type v) extends Applicative m where
    -- return is a keyword so don't use it
    /- Basically equivalent to pure from applicative. -/
    ret : α → m α
    bind : m α → (α → m β) → m β
    /- Drop the action on the left and only return the right one. If
       left contains e.g. a sideffect it will still be executed. -/
    and_then {α β : Type u} : m α → m β → m β := λ a1 a2 => bind a1 (Function.const α a2)

  export Monad (ret)

  infixl:65 " >>= " => Monads.Monad.bind
  infixl:60 " >> " => Monads.Monad.and_then

  /- Establishes some well behavedeness for ret and bind as well as a relation
     to apply and pure from applicative. -/
  class LawfulMonad (m : Type u → Type v) [mon: Monad m] extends LawfulApplicative m : Prop where
    /- Binding a pure value to a function should be the same as applying the function
       to the value directly -/
    ret_left_id : ∀ (a : α) (h : α → m β), ret a >>= h = h a
    /- Binding a monadic value to ret should be a no op -/
    ret_right_id : ∀ (a : m α), a >>= ret = a
    /- A modified associativity law for bind -/
    bind_assoc : ∀ (a : m α) (g : α → m β) (h : β → m γ), (a >>= g) >>= h = a >>= (λ x => g x >>= h)
    /- Pure and return should behave equivalently -/
    pure_behaved : ∀ (a : α), pure a = mon.ret a
    /- Apply and bind are related in this way as shown below -/
    apply_behaved : ∀ {α β : Type u} (mf : m (α → β)) (ma : m α), mf <*> ma = mf >>= (λ f => ma >>= (λ a => ret $ f a))
    /- and_then and seq_right are the same.-/
    and_then_behaved: ∀ (a1 : m α) (a2 : m β), a1 *> a2 = a1 >> a2

  namespace LawfulMonad
    variable {m : Type u → Type v} [monad : Monad m] [LawfulMonad m]
    -- Constructing a lawful applicative from a lawful monad
    -- pure is just return so don't define it explicitly
    def bind_apply {α β : Type u} :  m (α → β) → m α → m β
    | mf, ma => mf >>= (λ f => ma >>= (λ a => ret $ f a))

    -- law 1
    example : ∀ x : m α, bind_apply (ret id) x = x := by
      intro x
      simp only [bind_apply]
      rw [ret_left_id]
      simp only [id]
      rw [ret_right_id]

    -- law 2
    example : ∀ (x : α) (g : α → β), bind_apply (ret g) (ret x) = monad.ret (g x) := by
      intro x g
      simp only [bind_apply]
      rw [ret_left_id]
      rw [ret_left_id]

    -- law 3
    example : ∀ {α β : Type u} (x : α) (g : m (α → β)), bind_apply g (ret x) = bind_apply (ret (· $ x)) g := by
      intro α β x g
      simp only [bind_apply]
      simp only [ret_left_id]

    -- law 4 (a very automated proof since its just a definition massacre)
    example : ∀ {α β γ: Type u} (x : m (β → γ)) (y : m (α → β)) (z : m α), bind_apply (bind_apply (bind_apply (ret (@Function.comp α β γ)) x) y) z = bind_apply x (bind_apply y z) := by
      intro α β γ x y z
      simp only [bind_apply]
      simp only [ret_left_id, bind_assoc]
  end LawfulMonad
end Monads
