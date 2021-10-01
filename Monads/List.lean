import Monads.Functor
import Monads.Applicative
import Monads.Monad

namespace Monads
  inductive List (α : Type u) where
  | nil : List α
  | cons : α → List α → List α
    deriving Repr

  namespace List
    section Functor
      def map {α β : Type u} : (α → β) → (List α) → (List β)
      | f, nil => nil
      | f, (cons x xs) => cons (f x) (map f xs)

      #eval map (Nat.add 2) (cons 1 (cons 2 nil))
      
      theorem map_nil (f : α → β) : map f nil = nil := by rfl
      theorem map_cons (f : α → β) (x : α) (xs : List α) : map f (cons x xs) = cons (f x) (map f xs) := by rfl
      theorem map_id_eq_id {xs : List α} : map id xs = xs := by
        induction xs with
        | nil =>
          rw [map_nil]
        | cons x xs ih =>
          rw [map_cons]
          rw [ih]
          rw [id_eq]

      instance : Functor List where
        fmap := map

      theorem fmap_def (f : α → β) (xs : List α) : f <$> xs = map f xs := by rfl
        
      instance : LawfulFunctor List where
        fmap_id := by
          intro α xs
          induction xs with
          | nil =>
            rw [fmap_def, map_nil]
          | cons y ys ih =>
            rw [fmap_def, map_cons]
            rw [id_eq]
            rw [←fmap_def]
            rw [ih]
        fmap_comp := by
          intro α β γ g h xs
          induction xs with
          | nil =>
            rw [fmap_def, map_nil]
            rw [fmap_def g nil, map_nil]
            rw [fmap_def, map_nil]
          | cons y ys ih =>
            rw [fmap_def, map_cons]
            rw [fmap_def g, map_cons]
            rw [fmap_def, map_cons]
            rw [←fmap_def, ←fmap_def, ←fmap_def]
            rw [ih]
         map_const_behaved := by
           -- Still the default definition so the proof is automated
           intro α β x y
           simp only [Functor.map_const, Functor.fmap]
    end Functor

    section Applicative
      def append : List α → List α → List α
      | nil, ys => ys
      | (cons x xs), ys => cons x (append xs ys)

      instance {α : Type u} : Append (List α) where
        append := append

      #eval (cons 1 (cons 2 nil)) ++ (cons 3 (cons 4 nil))

      theorem nil_append (ys : List α) : nil ++ ys = ys := by rfl
      theorem cons_append (x : α) (xs : List α) (ys : List α) : (cons x xs) ++ ys = (cons x (xs ++ ys)) := by rfl
      theorem append_nil (xs : List α) : xs ++ nil = xs := by
        induction xs with
        | nil => rfl
        | cons x xs ih =>
          rw [cons_append]
          rw [ih]

      theorem append_assoc {xs ys zs : List α} : xs ++ ys ++ zs = xs ++ (ys ++ zs) := by
        induction xs with
        | nil =>
          rw [nil_append]
          rw [nil_append]
        | cons x xs ih =>
          rw [cons_append]
          rw [cons_append]
          rw [cons_append]
          rw [ih]

      theorem append_eq_of_suffix (as bs cs : List α) : (as = bs)  → (as ++ cs = bs ++ cs) := by
        intro h
        rw [h]

      def apply { α β : Type u} : List (α → β) → List α → List β
      | (cons f fs), xs => (f <$> xs) ++ (apply fs xs)
      | _, _ => nil

      instance : Applicative List where
        pure := λ x => (cons x nil)
        apply := apply

      theorem pure_def (x : α) : pure x = (cons x nil) := by rfl
      theorem apply_def {α β : Type u} (fs : List (α → β)) (xs : List α) : fs <*> xs = apply fs xs := by rfl
      theorem cons_apply {α β : Type u} (f : α → β) (fs : List (α → β)) (xs : List α) : (cons f fs) <*> xs = (f <$> xs) ++ (fs <*> xs) := by rfl
      theorem apply_nil {α β : Type u} (fs : List (α → β)) : fs <*> nil = nil := by
        induction fs with
        | nil => rfl
        | cons f fs ih =>
          rw [cons_apply]
          rw [ih]
          rw [append_nil]
          rw [fmap_def, map_nil]

      theorem nil_apply {α β: Type u} (xs : List α) : @nil (α → β) <*> xs = nil := by rfl

      #eval Nat.add <$> (cons 1 (cons 2 nil)) <*> (cons 3 (cons 4 nil))

      instance : LawfulApplicative List where
        apply_id := by
          intro α x
          rw [pure_def]
          rw [cons_apply]
          rw [nil_apply]
          rw [append_nil]
          rw [fmap_def, map_id_eq_id]
        apply_homomorphism := by
          intro α β x g
          rw [pure_def, pure_def, pure_def]
          rw [cons_apply]
          rw [nil_apply]
          rw [append_nil]
          rw [fmap_def, map_cons]
          rw [map_nil]
        apply_interchange := by
          intro α β x g
          rw [pure_def, pure_def]
          rw [cons_apply]
          rw [nil_apply]
          rw [append_nil]
          induction g with
          | nil =>
            rw [nil_apply]
            rw [fmap_def, map_nil]
          | cons g gs ih =>
            rw [cons_apply]
            rw [fmap_def, map_cons]
            rw [map_nil]
            rw [fmap_def, map_cons]
            rw [cons_append]
            rw [nil_append]
            rw [←fmap_def]
            rw [ih]
        apply_comp := sorry
        lifta2_behaved := by
          -- Definition wasn't changed -> auto proof
          intro α β γ g x y
          simp only [Applicative.liftA2, Applicative.apply]
        seq_right_behaved := by
          -- Definition wasn't changed -> auto proof
          intro α β a1 a2
          simp only [Applicative.seq_right, Applicative.apply]
        seq_left_behaved := by
          -- Definition wasn't changed -> auto proof
          intro α β a1 a2
          simp only [Applicative.seq_left, Applicative.liftA2]
        fmap_eq_pure_apply := by
          intro α β g x
          rw [pure_def]
          rw [cons_apply]
          rw [nil_apply]
          rw [append_nil]
    end Applicative

    section Monad
      def flatten : List (List α) → List α
      | nil => nil
      | (cons xs xss) => xs ++ flatten xss
      
      theorem flatten_nil : flatten nil = @nil α := by rfl
      theorem flatten_cons (xs : List α) (xss : List (List α)) : flatten (cons xs xss) = xs ++ flatten xss := by rfl

      def flat_map : List α → (α → List β) → List β
      | xs, f => flatten $ map f xs
      
      theorem flat_map_def (xs : List α) (f : α → List β) : flat_map xs f = (flatten $ map f xs) := by rfl
      theorem flat_map_nil (f : α → List β) : flat_map nil f = nil := by rfl
      theorem flat_map_cons (x : α) (xs : List α) (f : α → List β) : flat_map (cons x xs) f = (f x) ++ flat_map xs f := by
        rw [flat_map_def]
        rw [map_cons]
        rw [flatten_cons]
        rw [←flat_map_def]

      theorem flat_map_distrib_append {xs ys : List α} {f : α → List β} : flat_map (xs ++ ys) f = flat_map xs f ++ flat_map ys f := by
        induction xs with
        | nil =>
          rw [nil_append]
          rw [flat_map_nil]
          rw [nil_append]
        | cons x xs ih =>
          rw [cons_append]
          rw [flat_map_cons]
          rw [flat_map_cons]
          rw [ih]
          rw [append_assoc]
      theorem map_eq_constant_flat_map {α β : Type u} (f : α → β) (as : List α) : (map f as) = (flat_map as fun a => cons (f a) nil) := by
        induction as with
        | nil =>
          rw [map_nil]
          rw [flat_map_nil]
        | cons a as ih =>
          rw [map_cons]
          rw [flat_map_cons]
          rw [cons_append]
          rw [nil_append]
          rw [ih]

      instance : Monad List where
        ret := λ x => (cons x nil)
        bind := flat_map

      theorem ret_def (x : α) : ret x = cons x nil := by rfl
      theorem bind_def (xs : List α) (f : α → List β) : xs >>= f = flat_map xs f := by rfl

      #eval (cons 1 (cons 2 nil)) >>= (λ x => (cons x (cons x nil)))

      instance : LawfulMonad List where
        ret_left_id := by
          intro α β a h
          rw [ret_def]
          rw [bind_def, flat_map_def]
          rw [map_cons]
          rw [map_nil]
          rw [flatten_cons]
          rw [flatten_nil, append_nil]
        ret_right_id := by
          intro α as
          rw [bind_def]
          induction as with
          | nil =>
            rw [flat_map_nil]
          | cons a as ih =>
            rw [flat_map_cons]
            rw [ih]
            rw [ret_def]
            rw [cons_append]
            rw [nil_append]
        bind_assoc := by
          intro α β γ as g h
          induction as with
          | nil =>
            rw [bind_def nil, flat_map_nil]
            rw [bind_def nil, flat_map_nil]
            rw [bind_def nil, flat_map_nil]
          | cons x xs ih =>
            rw [bind_def (cons x xs), flat_map_cons]
            rw [bind_def (cons x xs), flat_map_cons]
            rw [←bind_def]
            rw [←bind_def]
            rw [←ih]
            rw [bind_def _ h]
            rw [flat_map_distrib_append]
            rw [←bind_def]
            rw [←bind_def]
        pure_behaved := by
          intro α a
          rw [pure_def, ret_def]
        apply_behaved := by
          intro α β mf ma
          induction mf with
          | nil =>
            rw [nil_apply]
            rw [bind_def, flat_map_nil]
          | cons f fs fih =>
            rw [cons_apply]
            rw [bind_def, flat_map_cons]
            rw [←bind_def]
            induction ma with
            | nil =>
              rw [fmap_def, map_nil]
              rw [nil_append]
              rw [apply_nil]
              rw [bind_def, flat_map_nil]
              rw [nil_append]
              rw [←fih]
              rw [apply_nil]
            | cons a as aih =>
              rw [←fih]
              rw [bind_def, flat_map_cons]
              rw [ret_def]
              rw [cons_append]
              rw [nil_append]
              rw [fmap_def, map_cons]
              rw [map_eq_constant_flat_map]
              -- we have to rewrite inside a function which is easier with simp only
              simp only [ret_def]
        and_then_behaved := by
          intro α β a1 a2
          simp only [Monad.and_then, Applicative.seq_right]
          induction a1 with
          | nil =>
            simp only [Functor.map_const]
            simp only [Function.comp]
            rw [map_nil]
            rw [←apply_def, nil_apply]
            rw [flat_map_nil]
          | cons x xs xih =>
            rw [flat_map_cons]
            simp only [Function.const]
            simp only [Functor.map_const]
            simp only [Function.comp]
            rw [map_cons]
            simp only [Function.const]
            rw [←apply_def, cons_apply]
            rw [fmap_def, map_id_eq_id]
            rw [←xih]
            simp only [Functor.map_const]
            simp only [Function.comp]
            simp only [Function.const]
            rw [←apply_def]
    end Monad
  end List
end Monads
