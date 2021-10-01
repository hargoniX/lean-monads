namespace Monads
  /- Functors capture the notion of a regular computation being executed
     on values that are within another type.
     This type usually captures either the notion of a container, such
     as a list, or a context for a computation, such as receiving data
     from IO.-/
  class Functor (f : Type u → Type v) : Type (max (u+1) v) where
    fmap : (α → β) → f α → f β
    map_const : α → f β → f α := fmap ∘ (Function.const β)

  export Functor (fmap map_const)
  infixr:100 " <$> " => Monads.Functor.fmap
  infixr:90 " <$ " => Monads.Functor.map_const

  namespace Functor
    def const_map {α β : Type u} {f : Type u → Type v} [Functor f] : f β → α → f α := flip map_const
    infixr:90 " $> " => Monads.Functor.const_map
    def void {α : Type} {f : Type → Type} [Functor f] : f α → f Unit := map_const ()
  end Functor

  /- LawfulFunctor ensures the Functor is in fact only applying the function
    to the values and not performing additional computation or modification
    See Maybe.lean for an example why we need both laws to hold for a sensible
    functor. -/
  class LawfulFunctor (f : Type u → Type v) [Functor f] : Prop where
    /- If the function maps values to themselves the values in the functor
       shall remain unchanged -/
    fmap_id : ∀ (x : f α), id <$> x = x
    /- Applying two functions via fmap is the same as applying one composed function
       at once via fmap -/
    fmap_comp : ∀ (g : α → β) (h : β → γ) (x : f α), (h ∘ g) <$> x = h <$> g <$> x
    /- If there is a custom map_const implementation it has to behave like the
       default one. -/
    map_const_behaved: ∀ (x : α) (y : f β), x <$ y = (fmap ∘ (Function.const β)) x y

  namespace LawfulFunctor
    variable {f : Type u → Type v} [Functor f] [LawfulFunctor f]

    example {g : α → β} {x : f α} : g <$> (id <$> x) = g <$> x := by
      rw [fmap_id]

    example {g : α → β} {x : f α} : id <$> (g <$> x) = g <$> x := by
      rw [fmap_id]
  end LawfulFunctor
end Monads
