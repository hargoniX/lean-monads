import Monads.Functor
import Monads.Applicative
import Monads.Monad

namespace Monads

  inductive Maybe (α : Type u) where
  | none : Maybe α
  | some : α → Maybe α
    deriving Repr

  namespace Maybe
    section Functor
      def map {α β : Type u} : (α → β) → Maybe α → Maybe β
      | f, none => none
      | f, (some a) => (some $ f a)
      
      theorem map_none {f : α → β} : map f none = none := by rfl
      theorem map_some {f : α → β} {x : α} :  map f (some x) = (some (f x)) := by rfl
      theorem map_id {x : Maybe α} : map id x = x := by
        induction x with
        | none =>
          rw [map_none]
        | some x =>
          rw [map_some]
          rw [id_eq]

      #eval map (· + 2) (some 12)
      #eval map (· + 2) none

      instance : Functor Maybe where
        fmap := Maybe.map
        
      theorem fmap_def (f : α → β) (x : Maybe α) : f <$> x = map f x := by rfl

      instance : LawfulFunctor Maybe where
        fmap_id := by
          intro α x
          rw [fmap_def]
          rw [map_id]
        fmap_comp := by
          intro α β γ g h x
          rw [fmap_def, fmap_def, fmap_def]
          induction x with
          | none =>
            rw [map_none]
            rw [map_none]
            rw [map_none]
          | some x =>
            rw [map_some]
            rw [map_some]
            rw [map_some]
        map_const_behaved := by
          -- We didn't change the definition so the proof is trivial
          intro α β x y
          simp [map_const, fmap]

      section BadFunctor
        private def bad_fmap {α β : Type u} : (α → β) → Maybe α → Maybe β
        | _, _ => none

        -- First law says this should be (some 12) but it isn't
        #eval bad_fmap id (some 12)
        -- Second law holds though
        example : ∀ {α β γ : Type u} (g : α → β) (h : β → γ) (x : Maybe α), bad_fmap (h ∘ g) x = bad_fmap h (bad_fmap g x) := by
          intro α β γ g h x
          simp only [bad_fmap]
      end BadFunctor
    end Functor

    section Applicative
      #check Nat.add <$> (some 12)

      def apply {α β : Type u} : Maybe (α → β) → Maybe α → Maybe β
      | (some f), (some a) => (some (f a))
      | _, _ => none

      #eval apply (Nat.add <$> (some 12)) (some 13)
      
      theorem none_apply {x : Maybe α} : apply none x = @none β := by rfl
      theorem apply_none {α β : Type u} {f : Maybe (α → β)} : apply f none = none := by
        induction f with
        | none => rfl
        | some => rfl 
      theorem some_apply_some {α β : Type u} {f : α → β} {x : α} : apply (some f) (some x) = (some $ f x) := by rfl

      instance : Applicative Maybe where
        pure := some
        apply := apply

      theorem pure_def (x : α) : pure x = some x := by rfl
      theorem apply_def {α β : Type u} (f : Maybe (α → β)) (x : Maybe α) : f <*> x = apply f x := by rfl

      #eval Nat.add <$> (some 12) <*> (some 13)

      instance : LawfulApplicative Maybe where
        apply_id := by
          intro α x
          rw [pure_def]
          rw [apply_def]
          induction x with
          | none =>
            rw [apply_none]
          | some =>
            rw [some_apply_some]
            rw [id_eq]
        apply_homomorphism := by
          intro α β x g
          rw [pure_def, pure_def, pure_def]
          rw [apply_def, some_apply_some]
        apply_interchange := by
          intro α β x g
          rw [pure_def, pure_def]
          induction g with
          | none =>
            rw [apply_def, none_apply]
            rw [apply_def, apply_none]
          | some g =>
            rw [apply_def, some_apply_some]
            rw [apply_def, some_apply_some]
        apply_comp := by
          intro α β γ x y z
          rw [pure_def]
          induction x with
          | none =>
            rw [(apply_def none)] -- unwrap specifically the apply we want
            rw [none_apply]
            rw [(apply_def _ none)]
            rw [apply_none]
            rw [(apply_def none)]
            rw [none_apply, apply_def, none_apply]
          | some fx =>
            induction y with
            | none =>
              rw [(apply_def none)]
              rw [none_apply]
              rw [apply_def _ none, apply_none]
              rw [apply_def _ none, apply_none]
              rw [apply_def, none_apply]
            | some fy =>
              induction z with
              | none =>
                rw [(apply_def _ none)]
                rw [apply_none]
                rw [(apply_def _ none)]
                rw [apply_none]
                rw [apply_def, apply_none]
              | some vz =>
                rw [apply_def (some fy) (some vz), some_apply_some]
                rw [apply_def (some fx), some_apply_some]
                rw [apply_def _ (some fx), some_apply_some]
                rw [apply_def _ (some fy), some_apply_some]
                rw [apply_def, some_apply_some]
        lifta2_behaved := by
          intro α β γ g x y
          simp only [liftA2]
          rw [apply_def]
        seq_right_behaved := by
          intro α β a1 a2
          simp only [Applicative.seq_right]
          rw [apply_def]
        seq_left_behaved := by
          intro α β a1 a2
          simp only [Applicative.seq_left, Applicative.liftA2]
        fmap_eq_pure_apply := by
          intro α β g x
          rw [pure_def]
          induction x with
          | none =>
            rw [fmap_def, map_none]
            rw [apply_def, apply_none]
          | some x =>
            rw [fmap_def, map_some]
            rw [apply_def, some_apply_some]
    end Applicative

    section Monad
      def bind : Maybe α → (α → Maybe β) → Maybe β
      | none, f => none
      | (some x), f => f x
      
      def none_bind (f : α → Maybe β) : bind none f = none := by rfl
      def some_bind (x : α) (f : α → Maybe β) : bind (some x) f = f x := by rfl

      instance : Monad Maybe where
        ret := some
        bind := bind
        
      theorem ret_def (x : α) : ret x = some x := by rfl
      theorem bind_def (x : Maybe α) (f : α → Maybe β) : x >>= f = bind x f := by rfl

      instance : LawfulMonad Maybe where
        ret_left_id := by
          intro α β a h
          rw [ret_def]
          rw [bind_def, some_bind]
        ret_right_id := by
          intro α a
          induction a with
          | none =>
            rw [bind_def, none_bind]
          | some a =>
            rw [bind_def, some_bind]
            rw [ret_def]
        bind_assoc := by
          intro α β γ a g h
          induction a with
          | none =>
            rw [bind_def none, none_bind]
            rw [bind_def none, none_bind]
            rw [bind_def none, none_bind]
          | some a =>
            rw [bind_def (some a), some_bind]
            rw [bind_def (some a), some_bind]
        pure_behaved := by
          intro α a
          rw [pure_def, ret_def]
        apply_behaved := by
          intro α β mf ma
          induction mf with
          | none =>
            rw [apply_def none, none_apply]
            rw [bind_def none, none_bind]
          | some f =>
            induction ma with
            | none =>
              rw [apply_def, apply_none]
              rw [bind_def, some_bind]
              rw [bind_def, none_bind]
            | some a =>
              rw [apply_def, some_apply_some]
              rw [bind_def, some_bind]
              rw [bind_def, some_bind]
              rw [ret_def]
        and_then_behaved := by
          intro α β a1 a2
          simp only [Applicative.seq_right, Monad.and_then]
          induction a1 with
          | none =>
            rw [none_bind]
            simp only [Functor.map_const]
            simp only [Function.comp]
            rw [map_none]
            rw [none_apply]
          | some x1 =>
            induction a2 with
            | none =>
              rw [apply_none]
              rw [some_bind]
            | some x2 =>
              simp only [Functor.map_const]
              simp only [Function.comp]
              rw [map_some]
              rw [some_apply_some]
              simp only [Function.const]
              rw [id_eq]
              rw [some_bind]
    end Monad
  end Maybe
end Monads
