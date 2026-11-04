(* Minus relation for words in Lambek calculus *)

Inductive Minus : Word -> Prop := 
  | mvi : forall v ne, (Nat.Odd ne) -> Minus ([BL v ne])
  | mmm : forall A B, (Minus A) -> (Minus B) -> (Minus (A++B))
  | pmm : forall A B, (Plus A) -> (Minus B) -> (Minus (A++B)).
